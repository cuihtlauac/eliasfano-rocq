#!/usr/bin/env bash
# Benchmark A evaluation — runs inside the Docker container
#
# A theorem only counts if the KERNEL certifies it proves the verbatim
# conjecture statement from the spec (Lemma <name>_stmt_check : <extracted
# statement>. Proof. exact <agent theorem>. Qed.) — grep-matching names
# alone would let an agent pass with a renamed or weakened statement.
# Additionally, the workspace spec must match the canonical copy baked
# into the image, and any spec definition the implementation restates
# must be definitionally equal to the spec's.
set -euo pipefail

WORKSPACE="${1:-/workspace}"
# Canonical (agent-unwritable) spec baked into the image.
# Override with CANONICAL_SPEC for local runs.
CANONICAL_SPEC="${CANONICAL_SPEC:-/home/vscode/task/theories/EliasFanoSpec.v}"
PROVED=0
TOTAL=8
SPEC_OK=1
DEFS_OK=1

# Each entry is "spec_name:pattern" where pattern matches the theorem name(s)
# The spec says nextGEQ_found but ground truth may use nextGEQ_found_thm etc.
THEOREMS=(
  "round_trip:round_trip"
  "access_correct:access_correct"
  "nextGEQ_found:nextGEQ_found"
  "nextGEQ_smallest:nextGEQ_smallest"
  "nextGEQ_none:nextGEQ_none"
  "space_bound:space_bound"
  "rank_select:rank_select"
  "select_rank:select_rank"
)

echo "=== Benchmark A: The Logical Core ==="
echo ""

# Step 1: Check EliasFano.v exists
if [ ! -f "$WORKSPACE/theories/EliasFano.v" ]; then
  echo "FAIL: theories/EliasFano.v not found"
  echo ""
  echo "Score: 0/$TOTAL"
  exit 1
fi

# Step 2: Build
echo "--- Building theories/ (timeout 30 min) ---"
cd "$WORKSPACE"
if timeout 1800 bash -c 'eval $(opam env) && dune build theories/ 2>&1'; then
  echo "PASS: dune build succeeded"
else
  echo "FAIL: dune build failed or timed out"
  echo ""
  echo "Score: 0/$TOTAL"
  exit 1
fi
echo ""

# Step 3: Spec integrity — the agent must not have modified the spec
echo "--- Checking spec integrity ---"
if [ -f "$CANONICAL_SPEC" ]; then
  if diff -q "$CANONICAL_SPEC" "$WORKSPACE/theories/EliasFanoSpec.v" >/dev/null 2>&1; then
    echo "PASS: EliasFanoSpec.v matches the canonical spec"
  else
    echo "FAIL: EliasFanoSpec.v differs from the canonical spec"
    SPEC_OK=0
  fi
  SPEC_SRC="$CANONICAL_SPEC"
else
  echo "WARN: canonical spec not found ($CANONICAL_SPEC); using workspace copy"
  SPEC_SRC="$WORKSPACE/theories/EliasFanoSpec.v"
fi
echo ""

# Step 4: Check for Admitted
ADMITTED_COUNT=$(grep -cE 'Admitted\.' "$WORKSPACE/theories/EliasFano.v" || true)
ADMITTED_COUNT=${ADMITTED_COUNT:-0}
if [ "$ADMITTED_COUNT" -gt 0 ]; then
  echo "WARN: $ADMITTED_COUNT Admitted found in EliasFano.v"
else
  echo "PASS: No Admitted in EliasFano.v"
fi
echo ""

# Find the coqc binary (needed by the compile checks below)
COQC="coqc"
eval $(opam env)
if ! command -v "$COQC" &>/dev/null; then
  COQC="rocqc"
fi

CHECK_DIR=$(mktemp -d)
trap 'rm -rf "$CHECK_DIR"' EXIT

# Prelude reproducing the spec's parsing environment (its own Require/
# Import/Open Scope lines, in order), then the modules under test —
# implementation last, so its definitions shadow the spec's Parameters.
{
  grep -E '^(From [A-Za-z].* Require|Import |Open Scope )' "$SPEC_SRC"
  echo "From EliasFano Require Import EliasFanoSpec EliasFano."
} > "$CHECK_DIR/prelude.v"

# Extract the verbatim statement of a conjecture from the spec.
extract_conjecture() {
  awk -v name="$1" '
    !found && $0 ~ ("^Conjecture " name " :") {
      found=1
      sub("^Conjecture " name " :", "")
      if ($0 ~ /[^[:space:]]/) print
      if ($0 ~ /\.[[:space:]]*$/) exit
      next
    }
    found { print; if ($0 ~ /\.[[:space:]]*$/) exit }
  ' "$SPEC_SRC"
}

# Step 5: Check each theorem proves the verbatim conjecture statement
echo "--- Checking theorems (kernel-verified statements) ---"
for entry in "${THEOREMS[@]}"; do
  spec_name="${entry%%:*}"
  pattern="${entry##*:}"
  # Accept Theorem/Lemma/Corollary, and allow _thm suffix or other variants
  actual=$(grep -oE "^(Theorem|Lemma|Corollary)\s+${pattern}(_thm)?\b" \
    "$WORKSPACE/theories/EliasFano.v" | head -1 | awk '{print $2}' || true)
  if [ -z "$actual" ]; then
    echo "FAIL: $spec_name not found"
    continue
  fi
  stmt=$(extract_conjecture "$spec_name")
  if [ -z "$stmt" ]; then
    echo "FAIL: $spec_name — could not extract conjecture from spec"
    continue
  fi
  {
    cat "$CHECK_DIR/prelude.v"
    echo "Lemma ${spec_name}_stmt_check :"
    echo "$stmt"
    echo "Proof. exact ${actual}. Qed."
  } > "$CHECK_DIR/Stmt_${spec_name}.v"
  if out=$(cd "$WORKSPACE" && $COQC -Q _build/default/theories EliasFano \
      "$CHECK_DIR/Stmt_${spec_name}.v" 2>&1); then
    echo "PASS: $spec_name ($actual proves the verbatim statement)"
    PROVED=$((PROVED + 1))
  else
    echo "FAIL: $spec_name — '$actual' does not prove the conjectured statement:"
    echo "$out" | head -4 | sed 's/^/    /'
  fi
done
echo ""

# Step 6: Spec definitions restated in the implementation must be identical.
# (The statement checks above resolve names to the implementation's
# definitions; this step certifies those mean the same as the spec's.)
echo "--- Checking restated spec definitions ---"
DEFS=$(grep -oE '^(Definition|Fixpoint) [A-Za-z0-9_]+' "$SPEC_SRC" | awk '{print $2}')
for d in $DEFS; do
  printf 'From EliasFano Require EliasFano.\nCheck EliasFano.%s.\n' "$d" \
    > "$CHECK_DIR/Has_$d.v"
  if ! (cd "$WORKSPACE" && $COQC -Q _build/default/theories EliasFano \
      "$CHECK_DIR/Has_$d.v" >/dev/null 2>&1); then
    echo "SKIP: $d (not redefined; implementation uses the spec's)"
    continue
  fi
  printf 'From EliasFano Require EliasFanoSpec EliasFano.\nLemma %s_def_check : EliasFanoSpec.%s = EliasFano.%s.\nProof. reflexivity. Qed.\n' \
    "$d" "$d" "$d" > "$CHECK_DIR/Def_$d.v"
  if (cd "$WORKSPACE" && $COQC -Q _build/default/theories EliasFano \
      "$CHECK_DIR/Def_$d.v" >/dev/null 2>&1); then
    echo "PASS: $d identical to spec"
  else
    echo "FAIL: $d redefined differently from the spec"
    DEFS_OK=0
  fi
done
echo ""

# Step 7: Print Assumptions check
echo "--- Checking axioms (Print Assumptions) ---"
ASSUMPTIONS_FILE="$CHECK_DIR/CheckAssumptions.v"
# Use only the theorems that actually exist in the file
{
  echo "From EliasFano Require Import EliasFano."
  for entry in "${THEOREMS[@]}"; do
    pattern="${entry##*:}"
    # Find the actual name used
    actual=$(grep -oE "^(Theorem|Lemma|Corollary)\s+${pattern}(_thm)?\b" \
      "$WORKSPACE/theories/EliasFano.v" | head -1 | awk '{print $2}' || true)
    if [ -n "$actual" ]; then
      echo "Print Assumptions ${actual}."
    fi
  done
} > "$ASSUMPTIONS_FILE"

cd "$WORKSPACE"
ASSUMPTIONS_OUTPUT=$($COQC -Q _build/default/theories EliasFano "$ASSUMPTIONS_FILE" 2>&1 || true)

# Keep only axiom name-lines ("name : ..." at column 0); the indented
# continuation lines of an axiom's type are not informative.
# Only popcount_spec + Uint63/PArray primitives are acceptable.
UNEXPECTED=$(echo "$ASSUMPTIONS_OUTPUT" | \
  grep -E '^[A-Za-z_][A-Za-z0-9_.'\'']* :' | \
  grep -v "popcount_spec" | \
  grep -v "Uint63" | \
  grep -v "PArray" | \
  grep -v "ArrayAxioms" | \
  grep -v "Int63" | \
  grep -v "Prim" || true)
if [ -z "$UNEXPECTED" ]; then
  echo "PASS: No unexpected axioms"
else
  echo "WARN: Potential unexpected axioms:"
  echo "$UNEXPECTED"
fi
echo ""

# Summary
echo "=== Results ==="
echo "Build: PASS"
echo "Spec integrity: $([ "$SPEC_OK" -eq 1 ] && echo PASS || echo FAIL)"
echo "Restated definitions: $([ "$DEFS_OK" -eq 1 ] && echo PASS || echo FAIL)"
echo "Admitted: $ADMITTED_COUNT"
echo "Theorems proved (statement-verified): $PROVED/$TOTAL"
echo ""
if [ "$PROVED" -eq "$TOTAL" ] && [ "$ADMITTED_COUNT" -eq 0 ] \
   && [ "$SPEC_OK" -eq 1 ] && [ "$DEFS_OK" -eq 1 ]; then
  echo "VERDICT: FULL PASS (8/8 statement-verified Qed, 0 Admitted)"
else
  echo "VERDICT: PARTIAL ($PROVED/$TOTAL statement-verified, $ADMITTED_COUNT Admitted, spec_ok=$SPEC_OK, defs_ok=$DEFS_OK)"
fi
