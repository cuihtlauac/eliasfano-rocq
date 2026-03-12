#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BUILD="$ROOT/_build/default/bench"
SUX="$SCRIPT_DIR/sux"

# Build everything
echo "=== Building ==="
PATH="$ROOT/_opam/bin:/usr/bin:/bin:$PATH" dune build bench/gen_data.exe bench/bench_ocaml.exe bench/bench_extracted.exe 2>/dev/null

if [ ! -f "$SUX/bench_sux" ]; then
  echo "Compiling Sux benchmark..."
  g++ -std=c++20 -O3 -DNDEBUG -march=native \
    -I"$SUX/sux-repo" \
    "$SUX/bench_sux.cpp" -o "$SUX/bench_sux"
fi

echo ""

oracle_check() {
  local ref_file="$1" check_file="$2" ref_prefix="$3" check_prefix="$4"
  local MISMATCHES=0
  while IFS= read -r ref_line; do
    if [[ "$ref_line" == ${ref_prefix}\ access* ]] || [[ "$ref_line" == ${ref_prefix}\ nextGEQ* ]] || [[ "$ref_line" == ${ref_prefix}\ decode_check* ]]; then
      query=$(echo "$ref_line" | sed "s/${ref_prefix} //" | sed 's/ \[.*$//')
      check_line=$(grep "${check_prefix} ${query%%=*}" "$check_file" 2>/dev/null | head -1 || true)
      if [ -n "$check_line" ]; then
        check_result=$(echo "$check_line" | sed "s/${check_prefix} //" | sed 's/ \[.*$//')
        if [ "$query" != "$check_result" ]; then
          echo "MISMATCH: ${ref_prefix}=$query vs ${check_prefix}=$check_result"
          MISMATCHES=$((MISMATCHES + 1))
        fi
      fi
    fi
  done < "$ref_file"
  if [ "$MISMATCHES" -eq 0 ]; then
    echo "OK: all results match"
  else
    echo "FAIL: $MISMATCHES mismatches"
  fi
}

# --- Test 1: Small data matching Rocq Compute checks ---
DATA=$(mktemp)
cat > "$DATA" <<'EOF'
3
7
42
---
access 0
access 1
access 2
nextGEQ 0
nextGEQ 5
nextGEQ 42
nextGEQ 43
EOF

echo "=== Test: [3, 7, 42], universe=100 ==="
echo "--- Sux (C++) ---"
"$SUX/bench_sux" < "$DATA" | tee "${DATA}.sux"
echo "--- OCaml hand-written ---"
"$BUILD/bench_ocaml.exe" < "$DATA" | tee "${DATA}.ocaml"
echo "--- OCaml extracted ---"
"$BUILD/bench_extracted.exe" < "$DATA" | tee "${DATA}.extracted"
echo "--- Oracle: sux vs hand-written ---"
oracle_check "${DATA}.sux" "${DATA}.ocaml" "sux" "ocaml"
echo "--- Oracle: sux vs extracted ---"
oracle_check "${DATA}.sux" "${DATA}.extracted" "sux" "extracted"
rm -f "$DATA" "${DATA}.sux" "${DATA}.ocaml" "${DATA}.extracted"
echo ""

# --- Test 2+: Generated data at increasing sizes ---
for N in 1000 10000 100000; do
  UNIVERSE=$((N * 10))
  SEED=42
  DATA=$(mktemp)

  echo "=== n=$N, universe=$UNIVERSE ==="
  "$BUILD/gen_data.exe" "$N" "$UNIVERSE" "$SEED" > "$DATA"

  echo "--- Sux (C++) ---"
  "$SUX/bench_sux" < "$DATA" | tee "${DATA}.sux"

  echo "--- OCaml hand-written ---"
  "$BUILD/bench_ocaml.exe" < "$DATA" | tee "${DATA}.ocaml"

  echo "--- OCaml extracted ---"
  "$BUILD/bench_extracted.exe" < "$DATA" | tee "${DATA}.extracted"

  echo "--- Oracle: sux vs hand-written ---"
  oracle_check "${DATA}.sux" "${DATA}.ocaml" "sux" "ocaml"
  echo "--- Oracle: sux vs extracted ---"
  oracle_check "${DATA}.sux" "${DATA}.extracted" "sux" "extracted"

  rm -f "$DATA" "${DATA}.sux" "${DATA}.ocaml" "${DATA}.extracted"
  echo ""
done
