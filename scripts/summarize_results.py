from __future__ import annotations

import argparse
import json
from pathlib import Path
from statistics import mean


def load_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as handle:
        return [json.loads(line) for line in handle if line.strip()]


def summarize(root: Path, data_root: Path) -> list[dict]:
    summaries: list[dict] = []
    labels = {
        item["name"]: item["gold"]
        for item in load_jsonl(data_root / "labels.jsonl")
    }
    for mode in ("single", "dual"):
        compact_path = root / f"{mode}.jsonl"
        if compact_path.exists():
            rows = load_jsonl(compact_path)
        else:
            paths = [
                root / f"set_{set_number:02d}" / mode / "results.jsonl"
                for set_number in range(1, 6)
            ]
            missing = [path for path in paths if not path.exists()]
            if missing:
                raise SystemExit(f"Missing result file: {missing[0]}")
            rows = [
                row
                for path in paths
                for row in load_jsonl(path)
            ]

        true_rows = [row for row in rows if labels[row["id"]] == "true"]
        false_rows = [row for row in rows if labels[row["id"]] == "false"]
        solved_true = [
            row for row in true_rows if row.get("final_status") == "solved"
        ]
        false_detected = [
            row for row in false_rows if row.get("final_status") == "false"
        ]
        false_positives = [
            row for row in true_rows if row.get("final_status") == "false"
        ]
        summaries.append(
            {
                "architecture": mode.capitalize(),
                "true_solved": len(solved_true),
                "true_not_solved": len(true_rows) - len(solved_true),
                "mean_rounds_to_solve": (
                    round(mean(row["rounds"] for row in solved_true), 2)
                    if solved_true
                    else None
                ),
                "false_detected": len(false_detected),
                "false_not_solved": len(false_rows) - len(false_detected),
                "false_positives": len(false_positives),
            }
        )
    return summaries


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--results-root",
        type=Path,
        default=Path("results/paper"),
    )
    parser.add_argument("--data-root", type=Path, default=Path("data"))
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    summaries = summarize(args.results_root, args.data_root)
    if args.json:
        print(json.dumps(summaries, ensure_ascii=False, indent=2))
        return 0

    print("| Architecture | True Solved | True Not Solved | Mean Rounds to Solve | False Detected | False Not Solved | False Positives |")
    print("|---|---:|---:|---:|---:|---:|---:|")
    for item in summaries:
        print(
            f"| {item['architecture']} | {item['true_solved']} | "
            f"{item['true_not_solved']} | {item['mean_rounds_to_solve']:.2f} | "
            f"{item['false_detected']} | {item['false_not_solved']} | "
            f"{item['false_positives']} |"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
