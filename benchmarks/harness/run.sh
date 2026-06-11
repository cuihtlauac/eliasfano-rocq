#!/usr/bin/env bash
# Benchmark harness — agent-agnostic orchestrator
#
# Usage:
#   ./run.sh <benchmark> [--build-only] [--eval-only <workspace>]
#
# Examples:
#   ./run.sh a                    # Build image, start container, wait for agent, evaluate
#   ./run.sh b --build-only       # Build Docker image only
#   ./run.sh a --eval-only /tmp/workspace  # Evaluate an existing workspace
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

usage() {
  echo "Usage: $0 <a|b> [OPTIONS]"
  echo ""
  echo "Benchmarks:"
  echo "  a    The Logical Core — prove 8 Z-level conjectures"
  echo "  b    The Implementation Gap — prove 5 Int63 agreement theorems"
  echo ""
  echo "Options:"
  echo "  --build-only          Build the Docker image and exit"
  echo "  --eval-only <path>    Skip Docker, evaluate artifacts at <path>"
  echo "  --ground-truth        Mount ground-truth solution for validation"
  echo "  --claude              Run Claude Code agent with retry loop"
  echo "  --model <model>       Claude model to use (default: sonnet)"
  echo "  --max-retries <n>     Max build-error retries (default: 5)"
  echo "  --max-turns <n>      Max Claude turns per attempt (default: 50)"
  exit 1
}

BENCHMARK="${1:-}"
[ -z "$BENCHMARK" ] && usage
shift

BUILD_ONLY=false
EVAL_ONLY=""
GROUND_TRUTH=false
USE_CLAUDE=false
MODEL="sonnet"
MAX_RETRIES=5
MAX_TURNS=50

while [ $# -gt 0 ]; do
  case "$1" in
    --build-only)    BUILD_ONLY=true; shift ;;
    --eval-only)     EVAL_ONLY="$2"; shift 2 ;;
    --ground-truth)  GROUND_TRUTH=true; shift ;;
    --claude)        USE_CLAUDE=true; shift ;;
    --model)         MODEL="$2"; shift 2 ;;
    --max-retries)   MAX_RETRIES="$2"; shift 2 ;;
    --max-turns)     MAX_TURNS="$2"; shift 2 ;;
    *)               usage ;;
  esac
done

case "$BENCHMARK" in
  a|b) ;;
  *)   echo "Error: benchmark must be 'a' or 'b'"; exit 1 ;;
esac

IMAGE_BASE="eliasfano-bench-base"
IMAGE_NAME="eliasfano-bench-${BENCHMARK}"
CONTAINER_NAME="eliasfano-bench-${BENCHMARK}-run"

# --- Evaluate existing workspace ---
if [ -n "$EVAL_ONLY" ]; then
  echo "Evaluating workspace: $EVAL_ONLY"
  bash "$SCRIPT_DIR/evaluate_${BENCHMARK}.sh" "$EVAL_ONLY"
  exit $?
fi

# --- Build base image ---
echo "=== Building base image: $IMAGE_BASE ==="
docker build \
  -t "$IMAGE_BASE" \
  -f "$ROOT_DIR/docker/Dockerfile.base" \
  "$ROOT_DIR"

if [ "$BUILD_ONLY" = true ] && [ "$BENCHMARK" = "base" ]; then
  echo "Base image built successfully."
  exit 0
fi

# --- Build benchmark image ---
echo ""
echo "=== Building benchmark image: $IMAGE_NAME ==="
docker build \
  -t "$IMAGE_NAME" \
  -f "$ROOT_DIR/docker/Dockerfile.${BENCHMARK}" \
  "$ROOT_DIR"

if [ "$BUILD_ONLY" = true ]; then
  echo "Image $IMAGE_NAME built successfully."
  exit 0
fi

# --- Run container ---
echo ""
echo "=== Starting container ==="

# Clean up any previous container
docker rm -f "$CONTAINER_NAME" 2>/dev/null || true

DOCKER_ARGS=(
  --name "$CONTAINER_NAME"
  --network host
)

if [ "$USE_CLAUDE" = true ]; then
  OUTPUT_DIR="$ROOT_DIR/results/${BENCHMARK}-$(date +%Y%m%dT%H%M%S)"
  mkdir -p "$OUTPUT_DIR"
  chmod 777 "$OUTPUT_DIR"

  # Copy credentials to temp dir readable/writable by container's vscode user (uid 1000).
  # Mount the whole .claude/ dir so session data persists across --resume calls.
  BENCH_HOME=$(mktemp -d)
  mkdir -p "$BENCH_HOME/.claude"
  cp "$HOME/.claude/.credentials.json" "$BENCH_HOME/.claude/"
  cp "$HOME/.claude.json" "$BENCH_HOME/"
  chmod -R a+rw "$BENCH_HOME"

  DOCKER_ARGS+=(--user 1000:1000)
  DOCKER_ARGS+=(-e CLAUDE_CODE_MAX_OUTPUT_TOKENS=128000)
  DOCKER_ARGS+=(-v "$(which claude):/usr/local/bin/claude:ro")
  DOCKER_ARGS+=(-v "$BENCH_HOME/.claude:/home/vscode/.claude")
  DOCKER_ARGS+=(-v "$BENCH_HOME/.claude.json:/home/vscode/.claude.json:ro")
  DOCKER_ARGS+=(-v "$SCRIPT_DIR/run_claude.sh:/run_claude.sh:ro")
  DOCKER_ARGS+=(-v "$ROOT_DIR/tasks/${BENCHMARK}/PROMPT.md:/PROMPT.md:ro")
  DOCKER_ARGS+=(-v "$OUTPUT_DIR:/output")
else
  DOCKER_ARGS+=(-it)
fi

if [ "$GROUND_TRUTH" = true ]; then
  echo "Mounting ground-truth solution for validation..."
  case "$BENCHMARK" in
    a)
      DOCKER_ARGS+=(-v "$ROOT_DIR/ground-truth/a/theories/EliasFano.v:/workspace/theories/EliasFano.v")
      ;;
    b)
      DOCKER_ARGS+=(-v "$ROOT_DIR/ground-truth/b/theories/EliasFanoInt63.v:/workspace/theories/EliasFanoInt63.v")
      ;;
  esac
fi

# Mount evaluation script
DOCKER_ARGS+=(-v "$SCRIPT_DIR/evaluate_${BENCHMARK}.sh:/evaluate.sh:ro")

if [ "$USE_CLAUDE" = true ]; then
  echo ""
  echo "=== Running Claude Code agent (model=$MODEL, max-retries=$MAX_RETRIES, max-turns=$MAX_TURNS) ==="
  echo "Output: $OUTPUT_DIR"
  echo "Monitor: tail -f $OUTPUT_DIR/run.log"
  echo ""

  docker run --rm "${DOCKER_ARGS[@]}" "$IMAGE_NAME" bash -c '
    export HOME=/home/vscode
    bash /run_claude.sh '"$BENCHMARK"' --model '"$MODEL"' --max-retries '"$MAX_RETRIES"' --max-turns '"$MAX_TURNS"'
    echo ""
    echo "=== Running evaluation ==="
    opam exec -- bash /evaluate.sh /workspace | tee /output/eval.log
    echo ""
    echo "=== Copying artifacts to /output ==="
    cp /workspace/theories/*.v /output/ 2>/dev/null || true
  '

  # Clean up temp credentials
  rm -rf "$BENCH_HOME"

  echo ""
  echo "Artifacts saved to: $OUTPUT_DIR"
  ls -l "$OUTPUT_DIR"
else
  echo ""
  echo "Container '$CONTAINER_NAME' is ready."
  echo ""
  echo "To run your agent:"
  echo "  docker exec -it $CONTAINER_NAME bash"
  echo ""
  echo "The agent workspace is at /workspace inside the container."
  echo "When the agent is done, evaluate with:"
  echo "  docker exec $CONTAINER_NAME bash /evaluate.sh"
  echo ""

  docker run "${DOCKER_ARGS[@]}" "$IMAGE_NAME" bash -c '
    echo "=== Elias-Fano Benchmark '"$BENCHMARK"' ==="
    echo "Workspace: /workspace"
    echo "Run your agent, then: bash /evaluate.sh"
    echo ""
    exec bash
  '

  # --- Evaluate ---
  echo ""
  echo "=== Running evaluation ==="
  docker exec "$CONTAINER_NAME" bash /evaluate.sh

  # Cleanup
  echo ""
  echo "Cleaning up container..."
  docker rm -f "$CONTAINER_NAME" 2>/dev/null || true
fi
