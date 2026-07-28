#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description="Select one public False problem per category.")
    parser.add_argument("--public", type=Path, required=True)
    parser.add_argument("--labels", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--split", default="hardfalse5")
    args = parser.parse_args()

    public_rows = {row["name"]: row for row in read_jsonl(args.public)}
    selected_labels: list[dict[str, Any]] = []
    seen: set[str] = set()
    for label in read_jsonl(args.labels):
        if label.get("gold") != "false":
            continue
        category = str(label.get("false_category", "")).strip()
        if category and category not in seen:
            selected_labels.append(label)
            seen.add(category)
    if len(selected_labels) != 5:
        raise ValueError(f"expected five False categories, found {sorted(seen)}")

    selected_public: list[dict[str, Any]] = []
    for label in selected_labels:
        row = dict(public_rows[label["name"]])
        row["split"] = args.split
        selected_public.append(row)
    args.output_dir.mkdir(parents=True, exist_ok=False)
    write_jsonl(args.output_dir / "problems.jsonl", selected_public)
    write_jsonl(args.output_dir / "labels.jsonl", selected_labels)
    write_jsonl(
        args.output_dir / "selection.jsonl",
        [
            {"position": index, "name": row["name"], "category": label["false_category"]}
            for index, (row, label) in enumerate(zip(selected_public, selected_labels, strict=True), start=1)
        ],
    )


if __name__ == "__main__":
    main()
