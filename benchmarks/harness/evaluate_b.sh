#!/usr/bin/env bash
# Benchmark B evaluation — runs inside the Docker container
#
# An agreement theorem only counts if the KERNEL certifies it proves the
# verbatim Conjecture statement from the canonical skeleton (via
# `exact`). The read-only inputs (EliasFanoSpec.v, EliasFano.v) must
# match their canonical copies, and the given implementations in the
# skeleton (Definition/Fixpoint/Record blocks) must appear verbatim in
# the agent's EliasFanoInt63.v — otherwise the agent could weaken a
# statement or trivialize the implementation being verified.
set -euo pipefail

WORKSPACE="${1:-/workspace}"
# Canonical (agent-unwritable) task files baked into the image.
# Override with CANONICAL_TASK_DIR for local runs.
CANONICAL_TASK_DIR="${CANONICAL_TASK_DIR:-/home/vscode/task/theories}"
SKELETON="$CANONICAL_TASK_DIR/EliasFanoInt63_skeleton.v"
PROVED=0
TOTAL=5
INPUTS_OK=1
IMPLS_OK=1

THEOREMS=(
  access63_agrees
  decode63_agrees
  nextGEQ63_found
  nextGEQ63_smallest
  nextGEQ63_none
)

echo "=== Benchmark B: The Implementation Gap ==="
echo ""

# Step 1: Check EliasFanoInt63.v exists
if [ ! -f "$WORKSPACE/theories/EliasFanoInt63.v" ]; then
  echo "FAIL: theories/EliasFanoInt63.v not found"
  echo ""
  echo "Score: 0/$TOTAL"
  exit 1
fi

# Step 2: Build
echo "--- Building theories/ (timeout 60 min) ---"
cd "$WORKSPACE"
if timeout 3600 bash -c 'eval $(opam env) && dune build theories/ 2>&1'; then
  echo "PASS: dune build succeeded"
else
  echo "FAIL: dune build failed or timed out"
  echo ""
  echo "Score: 0/$TOTAL"
  exit 1
fi
echo ""

# Step 3: Input integrity — read-only inputs must be unmodified
echo "--- Checking input integrity ---"
if [ -d "$CANONICAL_TASK_DIR" ]; then
  for f in EliasFanoSpec.v EliasFano.v; do
    if diff -q "$CANONICAL_TASK_DIR/$f" "$WORKSPACE/theories/$f" >/dev/null 2>&1; then
      echo "PASS: $f matches the canonical copy"
    else
      echo "FAIL: $f differs from the canonical copy"
      INPUTS_OK=0
    fi
  done
else
  echo "WARN: canonical task dir not found ($CANONICAL_TASK_DIR); skipping"
fi
echo ""

# Step 4: Given-implementation integrity — every Definition/Fixpoint/Record
# block of the skeleton must appear verbatim in the agent's file.
echo "--- Checking given implementations are unaltered ---"
if [ -f "$SKELETON" ]; then
  MODIFIED=0
  # bash substring containment: handles multi-line blocks literally
  # (grep -F would split a multi-line pattern into one-per-line patterns)
  IMPL_CONTENT=$(cat "$WORKSPACE/theories/EliasFanoInt63.v")
  while IFS= read -r name; do
    block=$(awk -v name="$name" '
      !found && $0 ~ ("^(Definition|Fixpoint|Record) " name "[ (]") {
        found=1; print
        if ($0 ~ /\.[[:space:]]*$/) exit
        next
      }
      found { print; if ($0 ~ /\.[[:space:]]*$/) exit }
    ' "$SKELETON")
    if [ -z "$block" ]; then
      echo "FAIL: could not extract given definition '$name' from skeleton"
      IMPLS_OK=0
      continue
    fi
    if [[ "$IMPL_CONTENT" != *"$block"* ]]; then
      echo "FAIL: given definition '$name' was modified"
      MODIFIED=$((MODIFIED + 1))
      IMPLS_OK=0
    fi
  done < <(grep -oE '^(Definition|Fixpoint|Record) [A-Za-z0-9_]+' "$SKELETON" | awk '{print $2}')
  if [ "$MODIFIED" -eq 0 ]; then
    DEF_COUNT=$(grep -cE '^(Definition|Fixpoint|Record) ' "$SKELETON" || true)
    echo "PASS: all $DEF_COUNT given definitions present verbatim"
  fi
else
  echo "WARN: canonical skeleton not found ($SKELETON); skipping"
fi
echo ""

# Step 5: Check for Admitted (excluding EliasFanoSpec.v)
ADMITTED_COUNT=0
for vfile in "$WORKSPACE"/theories/*.v; do
  basename=$(basename "$vfile")
  if [ "$basename" = "EliasFanoSpec.v" ]; then
    continue
  fi
  count=$(grep -c 'Admitted\.' "$vfile" 2>/dev/null || echo 0)
  if [ "$count" -gt 0 ]; then
    echo "WARN: $count Admitted in $basename"
    ADMITTED_COUNT=$((ADMITTED_COUNT + count))
  fi
done
if [ "$ADMITTED_COUNT" -eq 0 ]; then
  echo "PASS: No Admitted outside EliasFanoSpec.v"
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

# Step 6: Check each agreement theorem proves the verbatim skeleton statement
echo "--- Checking agreement theorems ---"
if [ -f "$SKELETON" ]; then
  # Prelude reproducing the skeleton's parsing environment, then the
  # module under test.
  {
    grep -E '^(From [A-Za-z].* Require|Import |Open Scope )' "$SKELETON"
    echo "From EliasFano Require Import EliasFanoInt63."
  } > "$CHECK_DIR/prelude.v"

  for thm in "${THEOREMS[@]}"; do
    if ! grep -qE "^(Theorem|Lemma|Corollary)\s+${thm}\b" \
        "$WORKSPACE/theories/EliasFanoInt63.v"; then
      echo "FAIL: $thm not found as proved theorem"
      continue
    fi
    stmt=$(awk -v name="$thm" '
      !found && $0 ~ ("^Conjecture " name " :") {
        found=1
        sub("^Conjecture " name " :", "")
        if ($0 ~ /[^[:space:]]/) print
        if ($0 ~ /\.[[:space:]]*$/) exit
        next
      }
      found { print; if ($0 ~ /\.[[:space:]]*$/) exit }
    ' "$SKELETON")
    if [ -z "$stmt" ]; then
      echo "FAIL: $thm — could not extract statement from skeleton"
      continue
    fi
    {
      cat "$CHECK_DIR/prelude.v"
      echo "Lemma ${thm}_stmt_check :"
      echo "$stmt"
      echo "Proof. exact ${thm}. Qed."
    } > "$CHECK_DIR/Stmt_${thm}.v"
    if out=$(cd "$WORKSPACE" && $COQC -Q _build/default/theories EliasFano \
        "$CHECK_DIR/Stmt_${thm}.v" 2>&1); then
      echo "PASS: $thm (proves the verbatim statement)"
      PROVED=$((PROVED + 1))
    else
      echo "FAIL: $thm — does not prove the skeleton's statement:"
      echo "$out" | head -4 | sed 's/^/    /'
    fi
  done
else
  # Fallback: name-only check (legacy behavior)
  for thm in "${THEOREMS[@]}"; do
    if grep -qE "^(Theorem|Lemma|Corollary)\s+${thm}\b" \
        "$WORKSPACE/theories/EliasFanoInt63.v"; then
      echo "PASS: $thm defined (name only — no canonical skeleton)"
      PROVED=$((PROVED + 1))
    else
      echo "FAIL: $thm not found as proved theorem"
    fi
  done
fi
echo ""

# Step 7: Print Assumptions check
echo "--- Checking axioms (Print Assumptions) ---"
ASSUMPTIONS_FILE="$CHECK_DIR/CheckAssumptions.v"
cat > "$ASSUMPTIONS_FILE" <<'ROCQ'
From EliasFano Require Import EliasFanoInt63.
Print Assumptions access63_agrees.
Print Assumptions decode63_agrees.
Print Assumptions nextGEQ63_found.
Print Assumptions nextGEQ63_smallest.
Print Assumptions nextGEQ63_none.
ROCQ

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
  echo "PASS: Only expected axioms (popcount_spec)"
else
  echo "WARN: Potential unexpected axioms:"
  echo "$UNEXPECTED"
fi
echo ""

# Step 8: Expansion factor (proof engineering metric)
echo "--- Expansion factor ---"
IMPL_LINES=$(grep -cE '^\s*(Definition|Fixpoint|Record|Let)\b' "$WORKSPACE/theories/EliasFanoInt63.v" 2>/dev/null || echo 0)
TOTAL_LINES=$(wc -l < "$WORKSPACE/theories/EliasFanoInt63.v" 2>/dev/null || echo 0)
echo "Total lines: $TOTAL_LINES"
echo "Definition lines: $IMPL_LINES"
echo ""

# Summary
echo "=== Results ==="
echo "Build: PASS"
echo "Input integrity: $([ "$INPUTS_OK" -eq 1 ] && echo PASS || echo FAIL)"
echo "Given implementations: $([ "$IMPLS_OK" -eq 1 ] && echo PASS || echo FAIL)"
echo "Admitted: $ADMITTED_COUNT"
echo "Agreement theorems proved (statement-verified): $PROVED/$TOTAL"
echo "Total lines: $TOTAL_LINES"
echo ""
if [ "$PROVED" -eq "$TOTAL" ] && [ "$ADMITTED_COUNT" -eq 0 ] \
   && [ "$INPUTS_OK" -eq 1 ] && [ "$IMPLS_OK" -eq 1 ]; then
  echo "VERDICT: FULL PASS (5/5 statement-verified agreements, 0 Admitted)"
else
  echo "VERDICT: PARTIAL ($PROVED/$TOTAL statement-verified, $ADMITTED_COUNT Admitted, inputs_ok=$INPUTS_OK, impls_ok=$IMPLS_OK)"
fi
