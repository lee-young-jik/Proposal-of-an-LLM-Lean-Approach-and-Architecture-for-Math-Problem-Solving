from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from .memory import JsonlTrialMemory
from .model import make_default_model_client
from .runtime import SingleOrchestrator
from .verifier import LakeVerifier


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run the single orchestrator Lean loop.")
    parser.add_argument("problem", nargs="?", help="Informal problem text.")
    parser.add_argument("--problem-file", type=Path, help="Read informal problem text from a file.")
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--memory-path", type=Path, default=Path(".runs/trial_memory.jsonl"))
    parser.add_argument("--model", help="Optional Codex model override.")
    parser.add_argument("--model-timeout", type=int, default=300, help="Seconds per model call; 0 disables the timeout.")
    parser.add_argument("--verify-timeout", type=int, default=60, help="Seconds per Lean build; 0 disables the timeout.")
    parser.add_argument(
        "--strict-timeout-guard",
        action="store_true",
        help=(
            "Reject timeout-sensitive tactics such as linarith/nlinarith "
            "before running Lean, so retries happen without spending the full "
            "verifier timeout."
        ),
    )
    parser.add_argument(
        "--max-trials",
        type=int,
        default=3,
        help="Maximum trials per orchestrator strategy round.",
    )
    parser.add_argument(
        "--max-strategy-rounds",
        type=int,
        default=3,
        help="Maximum orchestrator strategy rounds.",
    )
    args = parser.parse_args(argv)

    problem = _read_problem(args.problem, args.problem_file)
    project_root = args.project_root.resolve()
    memory_path = args.memory_path
    if not memory_path.is_absolute():
        memory_path = project_root / memory_path

    orchestrator = SingleOrchestrator(
        model_client=make_default_model_client(
            project_root,
            model=args.model,
            timeout_seconds=args.model_timeout,
        ),
        verifier=LakeVerifier(
            project_root=project_root,
            timeout_seconds=args.verify_timeout,
            strict_timeout_guard=args.strict_timeout_guard,
        ),
        memory=JsonlTrialMemory(memory_path),
        project_root=project_root,
        max_trials=args.max_trials,
        max_strategy_rounds=args.max_strategy_rounds,
    )
    result = orchestrator.run(problem)
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result["success"] else 1


def _read_problem(problem: str | None, problem_file: Path | None) -> str:
    if problem_file:
        return problem_file.read_text(encoding="utf-8")
    if problem:
        return problem
    if not sys.stdin.isatty():
        return sys.stdin.read()
    raise SystemExit("Provide a problem argument, --problem-file, or stdin.")
