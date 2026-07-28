from __future__ import annotations

import json
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def load_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as handle:
        return [json.loads(line) for line in handle if line.strip()]


def main() -> int:
    problems = load_jsonl(ROOT / "data" / "problems.jsonl")
    labels = load_jsonl(ROOT / "data" / "labels.jsonl")
    if len(problems) != 100 or len(labels) != 100:
        raise SystemExit("Expected 100 problems and 100 labels")
    if {item["name"] for item in problems} != {
        item["name"] for item in labels
    }:
        raise SystemExit("Problem and label IDs differ")

    for set_number in range(1, 6):
        set_name = f"set_{set_number:02d}"
        set_labels = [item for item in labels if item["set"] == set_name]
        if len(set_labels) != 20:
            raise SystemExit(f"{set_name}: expected 20 labels")
        gold_counts = Counter(item["gold"] for item in set_labels)
        if gold_counts != {"true": 10, "false": 10}:
            raise SystemExit(f"{set_name}: unexpected labels {gold_counts}")
        category_counts = Counter(
            item["false_category"]
            for item in set_labels
            if item["gold"] == "false"
        )
        if set(category_counts.values()) != {2} or len(category_counts) != 5:
            raise SystemExit(
                f"{set_name}: false categories are not balanced: {category_counts}"
            )
    expected_ids = {item["name"] for item in labels}
    for mode in ("single", "dual"):
        result_path = ROOT / "results" / "paper" / f"{mode}.jsonl"
        results = load_jsonl(result_path)
        if len(results) != 100:
            raise SystemExit(f"{result_path}: expected 100 results")
        if {item["id"] for item in results} != expected_ids:
            raise SystemExit(f"{result_path}: result and label IDs differ")
        if any("memory_path" in item for item in results):
            raise SystemExit(f"{result_path}: contains a machine-specific path")

    total_gold = Counter(item["gold"] for item in labels)
    total_categories = Counter(
        item["false_category"]
        for item in labels
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
