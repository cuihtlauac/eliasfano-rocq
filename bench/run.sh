#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BUILD="$ROOT/_build/default/bench"
SUX="$SCRIPT_DIR/sux"

# Build everything
echo "=== Building ==="
PATH="$ROOT/_opam/bin:/usr/bin:/bin:$PATH" dune build bench/gen_data.exe bench/bench_ocaml.exe 2>/dev/null

if [ ! -f "$SUX/bench_sux" ]; then
  echo "Compiling Sux benchmark..."
  g++ -std=c++20 -O3 -DNDEBUG -march=native \
    -I"$SUX/sux-repo" \
    "$SUX/bench_sux.cpp" -o "$SUX/bench_sux"
fi

echo ""

oracle_check() {
  local sux_file="$1" ocaml_file="$2"
  local MISMATCHES=0
  while IFS= read -r sux_line; do
    if [[ "$sux_line" == sux\ access* ]] || [[ "$sux_line" == sux\ nextGEQ* ]]; then
      query=$(echo "$sux_line" | sed 's/sux //' | sed 's/ \[.*$//')
      ocaml_line=$(grep "ocaml ${query%%=*}" "$ocaml_file" 2>/dev/null | head -1 || true)
      if [ -n "$ocaml_line" ]; then
        ocaml_result=$(echo "$ocaml_line" | sed 's/ocaml //' | sed 's/ \[.*$//')
        if [ "$query" != "$ocaml_result" ]; then
          echo "MISMATCH: sux=$query vs ocaml=$ocaml_result"
          MISMATCHES=$((MISMATCHES + 1))
        fi
      fi
    fi
  done < "$sux_file"
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
echo "--- OCaml (verified) ---"
"$BUILD/bench_ocaml.exe" < "$DATA" | tee "${DATA}.ocaml"
echo "--- Oracle comparison ---"
oracle_check "${DATA}.sux" "${DATA}.ocaml"
rm -f "$DATA" "${DATA}.sux" "${DATA}.ocaml"
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

  echo "--- OCaml (verified) ---"
  "$BUILD/bench_ocaml.exe" < "$DATA" | tee "${DATA}.ocaml"

  echo "--- Oracle comparison ---"
  oracle_check "${DATA}.sux" "${DATA}.ocaml"

  rm -f "$DATA" "${DATA}.sux" "${DATA}.ocaml"
  echo ""
done
