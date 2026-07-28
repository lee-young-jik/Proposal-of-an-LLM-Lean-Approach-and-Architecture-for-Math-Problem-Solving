#!/usr/bin/env python3
"""Split true/false JSONL inputs into reproducible balanced, shuffled sets."""

from __future__ import annotations

import argparse
import json
import random
import re
from pathlib import Path
from typing import Any


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open(encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, start=1):
            if not line.strip():
                continue
            value = json.loads(line)
            if not isinstance(value, dict):
                raise ValueError(f"{path}:{line_number}: expected a JSON object")
            rows.append(value)
    return rows


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--true-jsonl", type=Path, required=True)
    parser.add_argument("--false-jsonl", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--sets", type=int, default=10)
    parser.add_argument("--per-label", type=int, default=10)
    parser.add_argument("--seed", type=int, default=20260720)
    parser.add_argument("--split-prefix", default="balanced_mixed20")
    parser.add_argument(
        "--pair-by-name",
        action="store_true",
        help="Keep matching true/false variants in the same set.",
    )
    parser.add_argument(
        "--balance-false-field",
        help="Distribute false rows evenly by this field across every set.",
    )
    parser.add_argument(
        "--blind",
        action="store_true",
        help="Remove label metadata and replace public problem/theorem names.",
    )
    return parser.parse_args()


THEOREM_NAME_RE = re.compile(
    r"\b(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
HIDDEN_FIELDS = {
    "false_category",
    "false_transform",
    "false_fix",
    "source_true_name",
    "formal_repair",
    "expected_false_fix",
}


def blind_row(row: dict[str, Any], public_name: str) -> dict[str, Any]:
    public = {key: value for key, value in row.items() if key not in HIDDEN_FIELDS}
    public["name"] = public_name
    formal = public.get("formal_statement")
    if isinstance(formal, str):
        public["formal_statement"] = THEOREM_NAME_RE.sub(
            lambda match: f"{match.group(1)} {public_name}", formal, count=1
        )
    return public


def paired_base_name(row: dict[str, Any], prefix: str) -> str:
    name = row.get("name")
    if not isinstance(name, str) or not name.startswith(prefix):
        raise ValueError(f"expected row name starting with {prefix!r}; got {name!r}")
    return name.removeprefix(prefix)


def pair_rows(
    true_rows: list[dict[str, Any]], false_rows: list[dict[str, Any]]
) -> list[tuple[dict[str, Any], dict[str, Any]]]:
    true_by_base = {
        paired_base_name(row, "true_structural_"): row for row in true_rows
    }
    false_by_base = {
        paired_base_name(row, "false_structural_"): row for row in false_rows
    }
    if len(true_by_base) != len(true_rows) or len(false_by_base) != len(false_rows):
        raise ValueError("duplicate base problem name in paired inputs")
    if true_by_base.keys() != false_by_base.keys():
        missing_false = sorted(true_by_base.keys() - false_by_base.keys())
        missing_true = sorted(false_by_base.keys() - true_by_base.keys())
        raise ValueError(
            "paired inputs do not match: "
            f"missing false={missing_false}, missing true={missing_true}"
        )
    return [(true_by_base[base], false_by_base[base]) for base in true_by_base]


def main() -> None:
    args = parse_args()
    expected_per_label = args.sets * args.per_label
    true_rows = read_jsonl(args.true_jsonl)
    false_rows = read_jsonl(args.false_jsonl)

    if len(true_rows) != expected_per_label:
        raise ValueError(
            f"true input has {len(true_rows)} rows; expected {expected_per_label}"
        )
    if len(false_rows) != expected_per_label:
        raise ValueError(
            f"false input has {len(false_rows)} rows; expected {expected_per_label}"
        )

    rng = random.Random(args.seed)
    false_groups: dict[str, list[dict[str, Any]]] | None = None
    if args.balance_false_field:
        if args.pair_by_name:
            raise ValueError("--balance-false-field cannot be combined with --pair-by-name")
        false_groups = {}
        for row in false_rows:
            value = row.get(args.balance_false_field)
            if not isinstance(value, str) or not value:
                raise ValueError(
                    f"false row lacks string field {args.balance_false_field!r}: {row.get('name')!r}"
                )
            false_groups.setdefault(value, []).append(row)
        if args.per_label % len(false_groups) != 0:
            raise ValueError("per-label count must be divisible by the number of false groups")
        expected_group_size = args.sets * (args.per_label // len(false_groups))
        for value, rows in false_groups.items():
            if len(rows) != expected_group_size:
                raise ValueError(
                    f"false group {value!r} has {len(rows)} rows; expected {expected_group_size}"
                )
            rng.shuffle(rows)
    pairs = pair_rows(true_rows, false_rows) if args.pair_by_name else None
    if pairs is not None:
        rng.shuffle(pairs)
    else:
        rng.shuffle(true_rows)
        rng.shuffle(false_rows)
    args.output_dir.mkdir(parents=True, exist_ok=True)

    all_rows: list[dict[str, Any]] = []
    all_labels: list[dict[str, Any]] = []
    manifest_rows: list[dict[str, Any]] = []

    for set_index in range(args.sets):
        set_name = f"set_{set_index + 1:02d}"
        set_dir = args.output_dir / set_name
        set_dir.mkdir(exist_ok=False)
        start = set_index * args.per_label
        end = start + args.per_label
        if pairs is not None:
            set_pairs = pairs[start:end]
            tagged_rows = [
                (dict(true_row), "true", args.true_jsonl.name)
                for true_row, _ in set_pairs
            ] + [
                (dict(false_row), "false", args.false_jsonl.name)
                for _, false_row in set_pairs
            ]
        else:
            selected_false = false_rows[start:end]
            if false_groups is not None:
                per_group = args.per_label // len(false_groups)
                group_start = set_index * per_group
                group_end = group_start + per_group
                selected_false = [
                    row
                    for value in sorted(false_groups)
                    for row in false_groups[value][group_start:group_end]
                ]
            tagged_rows = [
                (dict(row), "true", args.true_jsonl.name)
                for row in true_rows[start:end]
            ] + [
                (dict(row), "false", args.false_jsonl.name)
                for row in selected_false
            ]
        rng.shuffle(tagged_rows)

        mixed_rows: list[dict[str, Any]] = []
        labels: list[dict[str, Any]] = []
        for position, (row, gold, source_file) in enumerate(tagged_rows, start=1):
            original_name = row.get("name")
            false_category = row.get("false_category")
            false_transform = row.get("false_transform")
            false_fix = row.get("false_fix") or row.get("expected_false_fix")
            if args.blind:
                row = blind_row(row, f"problem_{set_index + 1:02d}_{position:02d}")
            row["split"] = f"{args.split_prefix}_{set_name}"
            mixed_rows.append(row)
            label = {
                "set": set_name,
                "name": row.get("name"),
                "source_name": original_name,
                "gold": gold,
                "source_file": source_file,
            }
            if isinstance(false_category, str):
                label["false_category"] = false_category
            if gold == "false" and isinstance(false_transform, str) and false_transform:
                label["false_transform"] = false_transform
            if gold == "false" and isinstance(false_fix, list) and false_fix:
                label["expected_false_fix"] = [
                    str(item).strip() for item in false_fix if str(item).strip()
                ]
            labels.append(label)

        mixed_path = set_dir / "mixed20.jsonl"
        labels_path = set_dir / "labels.jsonl"
        write_jsonl(mixed_path, mixed_rows)
        write_jsonl(labels_path, labels)
        all_rows.extend(mixed_rows)
        all_labels.extend(labels)
        manifest_rows.append(
            {
                "set": set_name,
                "mixed20": str(mixed_path),
                "labels": str(labels_path),
                "true_count": args.per_label,
                "false_count": args.per_label,
            }
        )

    write_jsonl(args.output_dir / "manifest.jsonl", manifest_rows)
    write_jsonl(args.output_dir / "all_mixed200_by_sets.jsonl", all_rows)
    write_jsonl(args.output_dir / "all_labels_by_sets.jsonl", all_labels)
    metadata = {
        "seed": args.seed,
        "sets": args.sets,
        "per_label_per_set": args.per_label,
        "true_input": str(args.true_jsonl),
        "false_input": str(args.false_jsonl),
        "pair_by_name": args.pair_by_name,
        "balance_false_field": args.balance_false_field,
        "blind": args.blind,
        "total_rows": len(all_rows),
    }
    (args.output_dir / "metadata.json").write_text(
        json.dumps(metadata, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
