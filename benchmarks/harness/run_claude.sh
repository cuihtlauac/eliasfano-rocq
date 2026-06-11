#!/usr/bin/env bash
# Run Claude Code with retry loop on build errors
#
# Usage: run_claude.sh <benchmark> [--model MODEL] [--max-retries N]
#
# Runs inside the Docker container. Expects:
#   /PROMPT.md — task prompt
#   /workspace — writable workspace with dune project
#   /output   — mounted host directory for artifacts and logs
#   claude — on PATH
#   dune, coqc — on PATH (set by caller via opam env or explicit PATH)
#
# Monitor from host:
#   tail -f benchmarks/results/<run>/run.log
#   ls benchmarks/results/<run>/

set -euo pipefail

BENCHMARK="${1:?usage: run_claude.sh <a|b>}"; shift
MODEL="sonnet"
MAX_RETRIES=5
MAX_TURNS=50

while [ $# -gt 0 ]; do
  case "$1" in
    --model)       MODEL="$2"; shift 2 ;;
    --max-retries) MAX_RETRIES="$2"; shift 2 ;;
    --max-turns)   MAX_TURNS="$2"; shift 2 ;;
    *)             echo "Unknown option: $1"; exit 1 ;;
  esac
done

LOG=/output/run.log

log() {
  echo "$@" | tee -a "$LOG"
}

cd /workspace
SESSION_ID=""
BUILD_ERROR=""

# Expected output file per benchmark
case "$BENCHMARK" in
  a) EXPECTED_FILE="/workspace/theories/EliasFano.v" ;;
  b) EXPECTED_FILE="/workspace/theories/EliasFanoInt63.v" ;;
  *) EXPECTED_FILE="" ;;
esac

log "=== run_claude.sh: benchmark=$BENCHMARK model=$MODEL max_retries=$MAX_RETRIES max_turns=$MAX_TURNS ==="
log "Started: $(date -Iseconds)"
log "PATH=$PATH"
log "HOME=$HOME"

# Sanity checks
command -v claude >/dev/null || { log "FATAL: claude not found on PATH"; exit 1; }
command -v opam >/dev/null || { log "FATAL: opam not found on PATH"; exit 1; }

for attempt in $(seq 0 "$MAX_RETRIES"); do
  CLAUDE_STDERR="/output/claude_stderr_${attempt}.log"

  if [ "$attempt" -eq 0 ]; then
    log "[attempt $attempt] Sending task prompt..."
    RESPONSE=$(claude -p \
      --dangerously-skip-permissions \
      --model "$MODEL" \
      --output-format json \
      --max-turns "$MAX_TURNS" \
      "$(cat /PROMPT.md)" 2>"$CLAUDE_STDERR") || true
  else
    log "[attempt $attempt] Resuming with build error (session=$SESSION_ID)..."
    RESPONSE=$(claude -p \
      --dangerously-skip-permissions \
      --model "$MODEL" \
      --output-format json \
      --max-turns "$MAX_TURNS" \
      --resume "$SESSION_ID" \
      "The build failed. Here is the error:

$BUILD_ERROR

Fix the error and try again." 2>"$CLAUDE_STDERR") || true
  fi

  # Save Claude's response
  echo "$RESPONSE" > "/output/response_${attempt}.json"

  # Check for empty response
  if [ -z "$RESPONSE" ]; then
    log "[attempt $attempt] ERROR: claude returned empty response"
    log "stderr: $(cat "$CLAUDE_STDERR")"
    log "Aborting."
    exit 1
  fi

  SESSION_ID=$(echo "$RESPONSE" | jq -r '.session_id // empty')
  IS_ERROR=$(echo "$RESPONSE" | jq -r '.is_error // empty')
  COST=$(echo "$RESPONSE" | jq -r '.total_cost_usd // empty')
  TURNS=$(echo "$RESPONSE" | jq -r '.num_turns // empty')
  RESULT_MSG=$(echo "$RESPONSE" | jq -r '.result // empty' | head -c 200)
  if [ -z "$SESSION_ID" ]; then
    log "[attempt $attempt] WARNING: no session_id in response"
    log "response (first 500 chars): $(echo "$RESPONSE" | head -c 500)"
  else
    log "[attempt $attempt] session_id=$SESSION_ID turns=$TURNS cost=\$$COST is_error=$IS_ERROR"
  fi
  if [ "$IS_ERROR" = "true" ]; then
    log "[attempt $attempt] Claude error: $RESULT_MSG"
  fi

  # Snapshot .v files after this attempt
  mkdir -p "/output/attempts/$attempt"
  cp /workspace/theories/*.v "/output/attempts/$attempt/" 2>/dev/null || true

  log "[attempt $attempt] Claude finished. Trying build..."

  # Check expected file exists
  if [ -n "$EXPECTED_FILE" ] && [ ! -f "$EXPECTED_FILE" ]; then
    BUILD_ERROR="Expected file not found: $EXPECTED_FILE
Claude may have timed out or failed to write the file."
    echo "$BUILD_ERROR" > "/output/build_error_${attempt}.log"
    log "[attempt $attempt] BUILD FAILED: $EXPECTED_FILE not found"
    continue
  fi

  BUILD_OUTPUT=$(opam exec -- dune build theories/ 2>&1) && {
    log "[attempt $attempt] BUILD PASSED"
    log "Finished: $(date -Iseconds)"
    exit 0
  }

  BUILD_ERROR=$(echo "$BUILD_OUTPUT" | head -200)
  echo "$BUILD_OUTPUT" > "/output/build_error_${attempt}.log"
  log "[attempt $attempt] BUILD FAILED (see build_error_${attempt}.log):"
  log "$(echo "$BUILD_ERROR" | head -20)"
  log "..."
done

log "All $((MAX_RETRIES + 1)) attempts exhausted."
log "Finished: $(date -Iseconds)"
exit 1
