#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CONFIG="$ROOT/configs/paper_experiment.env"
SET_NUMBER=""
MODE="both"
CONFIRMED=false

usage() {
  cat <<'EOF'
Usage:
  scripts/run_paper_experiment.sh --set 01 [--mode single|dual|both] --run

The --run flag is required because this command makes paid model calls.
EOF
}

while (($#)); do
  case "$1" in
    --set)
      SET_NUMBER="${2:-}"
      shift 2
      ;;
    --mode)
      MODE="${2:-}"
      shift 2
      ;;
    --run)
      CONFIRMED=true
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "Unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if [[ "$CONFIRMED" != true ]]; then
  echo "Prepared only. Add --run to start paid model calls." >&2
  exit 2
fi
if [[ ! "$SET_NUMBER" =~ ^0[1-5]$ ]]; then
  echo "--set must be one of 01, 02, 03, 04, or 05." >&2
  exit 2
fi
if [[ "$MODE" != "single" && "$MODE" != "dual" && "$MODE" != "both" ]]; then
  echo "--mode must be single, dual, or both." >&2
  exit 2
fi

set -a
source "$CONFIG"
if [[ -f "$ROOT/.env" ]]; then
  source "$ROOT/.env"
fi
set +a

: "${OPENROUTER_API_KEY:?Set OPENROUTER_API_KEY in .env or the environment.}"

PYTHON_BIN="${PYTHON_BIN:-python3}"
MINIF2F_ROOT="${MINIF2F_ROOT:-$ROOT/.datasets/miniF2F-lean4}"
DATA_DIR="$ROOT/data/set_$SET_NUMBER"
OUTPUT_ROOT="${OUTPUT_ROOT:-$ROOT/.runs/paper/set_$SET_NUMBER}"
PRELUDE=$'import MiniF2F.ProblemImports\nopen scoped Real\nopen scoped Nat\nopen scoped Topology\nopen scoped Polynomial'
if ((10#$SET_NUMBER <= 3)); then
  MODEL_TIMEOUT="$MODEL_TIMEOUT_SETS_01_03"
else
  MODEL_TIMEOUT="$MODEL_TIMEOUT_SETS_04_05"
fi

if [[ ! -f "$MINIF2F_ROOT/MiniF2F/ProblemImports.lean" ]]; then
  echo "miniF2F was not found at $MINIF2F_ROOT." >&2
  echo "Run scripts/setup_minif2f.sh first." >&2
  exit 2
fi
command -v codex >/dev/null || {
  echo "Codex CLI is required for the OAuth-routed agents." >&2
  exit 2
}
command -v lake >/dev/null || {
  echo "Lean/Lake is required for verification." >&2
  exit 2
}

export PYTHONPATH="$ROOT/src"
export DUAL_ARC_MODEL_CLIENT=cli
export DUAL_ARC_DUAL_MEMORY_SCHEMA="$DUAL_MEMORY_SCHEMA"
export LANGSMITH_TRACING=false
export LANGCHAIN_TRACING_V2=false
unset DUAL_ARC_FALSE_REVIEW_PROJECT

common_args=(
  --jsonl "$DATA_DIR/mixed20.jsonl"
  --labels-jsonl "$DATA_DIR/labels.jsonl"
  --split "hard_balanced_mixed20_set_$SET_NUMBER"
  --limit 20
  --project-root "$MINIF2F_ROOT"
  --model "$NATURAL_MODEL"
  --orchestrator-model "$ORCHESTRATOR_MODEL"
  --false-judgment-model "$FALSE_REASON_MODEL"
  --nature-model "$NATURAL_MODEL"
  --lean-model "$LEAN_MODEL"
  --retry-model "$RETRY_MODEL"
  --strict-model-routing
  --model-timeout "$MODEL_TIMEOUT"
  --max-trials "$MAX_TRIALS"
  --verify-timeout "$VERIFY_TIMEOUT"
  --verifier-prelude "$PRELUDE"
)

run_single() {
  local out="$OUTPUT_ROOT/single"
  mkdir -p "$out"
  "$PYTHON_BIN" -m single_orchestrator.proofnet_cli \
    "${common_args[@]}" \
    --max-strategy-rounds "$MAX_ROUNDS" \
    --verifier-module "MiniF2F.Scratch.Set${SET_NUMBER}SingleGenerated" \
    --verifier-file "$MINIF2F_ROOT/MiniF2F/Scratch/Set${SET_NUMBER}SingleGenerated.lean" \
    --output-dir "$out" \
    --output "$out/results.jsonl" \
    2>&1 | tee "$out/run.log"
}

run_dual() {
  local out="$OUTPUT_ROOT/dual"
  mkdir -p "$out"
  "$PYTHON_BIN" -m single_orchestrator.dual_proofnet_cli \
    "${common_args[@]}" \
    --max-rounds "$MAX_ROUNDS" \
    --verifier-module "MiniF2F.Scratch.Set${SET_NUMBER}DualGenerated" \
    --verifier-file "$MINIF2F_ROOT/MiniF2F/Scratch/Set${SET_NUMBER}DualGenerated.lean" \
    --output-dir "$out" \
    --output "$out/results.jsonl" \
    2>&1 | tee "$out/run.log"
}

case "$MODE" in
  single) run_single ;;
  dual) run_dual ;;
  both)
    run_single
    run_dual
    ;;
esac

echo "Results written under $OUTPUT_ROOT"
