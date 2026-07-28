from __future__ import annotations

import argparse
import json
from pathlib import Path

from .false_review import FalseReviewRuntime
from .model import make_prompt_routing_model_client


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Run the isolated two-model False review test harness."
    )
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--reason-model", default="gpt-5.3-codex")
    parser.add_argument("--check-model", default="gpt-5.5")
    parser.add_argument("--model-timeout", type=int, default=300)
    args = parser.parse_args(argv)

    case = json.loads(args.case.read_text(encoding="utf-8"))
    memory = case.get("memory", [])
    answer_key = case.get("key", {})
    if not isinstance(memory, list) or not isinstance(answer_key, dict):
        raise SystemExit("case must contain a memory list and key object")

    client = make_prompt_routing_model_client(
        Path.cwd(),
        default_model=args.reason_model,
        timeout_seconds=args.model_timeout,
        prompt_models={"false_check": args.check_model},
    )
    result = FalseReviewRuntime(client).review(memory=memory, answer_key=answer_key)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
