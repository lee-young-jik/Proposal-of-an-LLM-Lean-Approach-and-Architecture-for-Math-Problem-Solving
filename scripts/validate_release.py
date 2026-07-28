from __future__ import annotations

import json
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def load_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as handle:
        return [json.loads(line) for line in handle if line.strip()]


def main() -> int:
    total_labels: list[dict] = []
    for set_number in range(1, 6):
        set_name = f"set_{set_number:02d}"
        data_dir = ROOT / "data" / set_name
        problems = load_jsonl(data_dir / "mixed20.jsonl")
        labels = load_jsonl(data_dir / "labels.jsonl")
        if len(problems) != 20 or len(labels) != 20:
            raise SystemExit(f"{set_name}: expected 20 problems and 20 labels")
        if {item["name"] for item in problems} != {
            item["name"] for item in labels
        }:
            raise SystemExit(f"{set_name}: problem and label IDs differ")
        gold_counts = Counter(item["gold"] for item in labels)
        if gold_counts != {"true": 10, "false": 10}:
            raise SystemExit(f"{set_name}: unexpected labels {gold_counts}")
        category_counts = Counter(
            item["false_category"]
            for item in labels
            if item["gold"] == "false"
        )
        if set(category_counts.values()) != {2} or len(category_counts) != 5:
            raise SystemExit(
                f"{set_name}: false categories are not balanced: {category_counts}"
            )
        for mode in ("single", "dual"):
            result_path = (
                ROOT / "results" / "paper" / set_name / mode / "results.jsonl"
            )
            results = load_jsonl(result_path)
            if len(results) != 20:
                raise SystemExit(f"{result_path}: expected 20 results")
            if any("memory_path" in item for item in results):
                raise SystemExit(f"{result_path}: contains a machine-specific path")
        total_labels.extend(labels)

    total_gold = Counter(item["gold"] for item in total_labels)
    total_categories = Counter(
        item["false_category"]
        for item in total_labels
        if item["gold"] == "false"
    )
    if total_gold != {"true": 50, "false": 50}:
        raise SystemExit(f"Unexpected total labels: {total_gold}")
    if set(total_categories.values()) != {10} or len(total_categories) != 5:
        raise SystemExit(f"Unexpected total category balance: {total_categories}")

    print("Release data and result files are internally consistent.")
    print(f"Gold labels: {dict(total_gold)}")
    print(f"False categories: {dict(sorted(total_categories.items()))}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
