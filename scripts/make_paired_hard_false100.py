#!/usr/bin/env python3
"""Create 100 harder paired False statements in five balanced families.

Every mutation changes the conclusion in a way incompatible with the source
theorem.  One family also rewrites a premise equivalently as camouflage.  The
mutation key is retained only in private metadata by the set splitter.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import json
from pathlib import Path
import random
import re
from typing import Any, Callable


THEOREM_NAME_RE = re.compile(r"\b(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b")
INT_RE = re.compile(r"(?<![A-Za-z0-9_'])\d+(?![A-Za-z0-9_'])")
CATEGORIES = (
    "nearby_answer_constant",
    "equality_relation_flip",
    "strict_order_contradiction",
    "trichotomy_branch_exclusion",
    "camouflaged_two_point_shift",
)
QUOTA = 20


@dataclass(frozen=True)
class Mutation:
    category: str
    formal_statement: str
    transform: str
    fix: tuple[str, ...]
    changed_fragments: tuple[tuple[str, str], ...]


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")


def split_proof(formal: str) -> tuple[str, str]:
    position = formal.rfind(" := by")
    return (formal.rstrip(), " := by") if position < 0 else (formal[:position].rstrip(), formal[position:])


def conclusion_start(head: str) -> int:
    depth = 0
    for index, char in enumerate(head):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        elif char == ":" and depth == 0:
            return index + 1
    return -1


def top_level_equality(body: str) -> int:
    depth = 0
    for index, char in enumerate(body):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and body[index : index + 3] == " = ":
            return index
    return -1


def numeric_target_mutation(formal: str, category: str) -> Mutation | None:
    parts = equality_parts(formal)
    if parts is None:
        return None
    prefix, left, right, tail = parts
    if any(token in right for token in ("∧", "∨", "↔", "∃", "∀", "Set")):
        return None
    matches = list(INT_RE.finditer(right))
    if not matches:
        return None
    match = matches[-1]
    old = match.group(0)
    old_value = int(old)
    # Avoid a single globally repeated delta while keeping the change local.
    delta = 2 if old_value % 3 == 0 else 1
    new = str(old_value + delta)
    mutated_right = right[: match.start()] + new + right[match.end() :]
    mutated = f"{prefix}{left} = {mutated_right}{tail}"
    return Mutation(
        category,
        mutated,
        f"changed a conclusion target `{old}` to the nearby value `{new}`",
        (f"restore the conclusion target `{new}` to `{old}`",),
        ((old, new),),
    )


def equality_parts(formal: str) -> tuple[str, str, str, str] | None:
    head, tail = split_proof(formal)
    start = conclusion_start(head)
    if start < 0:
        return None
    prefix = head[:start]
    body = head[start:].strip()
    position = top_level_equality(body)
    if position < 0 or any(token in body for token in ("∃", "∀", "let ")):
        return None
    left = body[:position].strip()
    right = body[position + 3 :].strip()
    if not left or not right:
        return None
    return prefix, left, right, tail


def equality_flip_mutation(formal: str) -> Mutation | None:
    parts = equality_parts(formal)
    if parts is None:
        head, tail = split_proof(formal)
        start = conclusion_start(head)
        if start < 0:
            return None
        body = head[start:].strip()
        if not body:
            return None
        return Mutation(
            "equality_relation_flip",
            f"{head[:start]}¬ ({body}){tail}",
            "reversed the polarity of the complete non-equality conclusion",
            (f"replace `¬ ({body})` with `{body}`",),
            ((body, f"¬ ({body})"),),
        )
    prefix, left, right, tail = parts
    return Mutation(
        "equality_relation_flip",
        f"{prefix}{left} ≠ {right}{tail}",
        "replaced the conclusion equality with disequality",
        ("replace the conclusion relation `≠` with `=`",),
        (("=", "≠"),),
    )


def is_orderable_numeric_equality(left: str, right: str) -> bool:
    blocked = ("Set", "{", "}", "(", ",", "↔", "∧", "∨")
    # Parentheses are common in arithmetic, so only reject tuple-looking RHS.
    return not any(token in left + right for token in ("Set", "{", "}", "↔", "∧", "∨")) and not re.search(
        r"\([^()]*,[^()]*\)", right
    )


def strict_order_mutation(formal: str, direction: str) -> Mutation | None:
    parts = equality_parts(formal)
    if parts is None:
        return None
    prefix, left, right, tail = parts
    if not is_orderable_numeric_equality(left, right):
        return None
    relation = "<" if direction == "lt" else ">"
    return Mutation(
        "strict_order_contradiction",
        f"{prefix}{left} {relation} {right}{tail}",
        f"changed the exact conclusion equality to the strict relation `{relation}`",
        (f"replace the conclusion relation `{relation}` with `=`",),
        (("=", relation),),
    )


def trichotomy_mutation(formal: str) -> Mutation | None:
    parts = equality_parts(formal)
    if parts is None:
        return None
    prefix, left, right, tail = parts
    if not is_orderable_numeric_equality(left, right):
        return None
    replacement = f"({left} < {right} ∨ {right} < {left})"
    return Mutation(
        "trichotomy_branch_exclusion",
        f"{prefix}{replacement}{tail}",
        "replaced equality by the two strict, non-equality branches of trichotomy",
        (f"replace `{replacement}` with `{left} = {right}`",),
        ((f"{left} = {right}", replacement),),
    )


def first_hypothesis_span(head: str) -> tuple[int, int, str] | None:
    stop = conclusion_start(head) - 1
    if stop < 0:
        return None
    depth = 0
    start: int | None = None
    for index, char in enumerate(head[:stop]):
        if char == "(":
            if depth == 0:
                start = index
            depth += 1
        elif char == ")" and depth:
            depth -= 1
            if depth == 0 and start is not None:
                text = head[start : index + 1]
                inner = text[1:-1]
                if ":" in inner:
                    names, proposition = inner.split(":", 1)
                    if all(name.startswith("h") for name in names.split()):
                        return start, index + 1, proposition.strip()
                start = None
    return None


def camouflaged_mutation(formal: str) -> Mutation | None:
    base = numeric_target_mutation(formal, "camouflaged_two_point_shift")
    if base is None:
        return None
    head, tail = split_proof(base.formal_statement)
    span = first_hypothesis_span(head)
    if span is None:
        return None
    start, stop, proposition = span
    original = head[start:stop]
    names = original[1:-1].split(":", 1)[0].strip()
    rewritten = f"({names} : ({proposition}) ∧ True)"
    statement = head[:start] + rewritten + head[stop:] + tail
    return Mutation(
        base.category,
        statement,
        base.transform + "; equivalently rewrote one premise with an added `∧ True` decoy",
        base.fix,
        base.changed_fragments + ((original, rewritten),),
    )


def candidates(formal: str, row_index: int) -> dict[str, Mutation]:
    strict = strict_order_mutation(formal, "lt" if row_index % 2 == 0 else "gt")
    values = (
        numeric_target_mutation(formal, "nearby_answer_constant"),
        equality_flip_mutation(formal),
        strict,
        trichotomy_mutation(formal),
        camouflaged_mutation(formal),
    )
    return {value.category: value for value in values if value is not None}


def balanced_assignment(all_candidates: list[dict[str, Mutation]]) -> list[str]:
    slots = [category for category in CATEGORIES for _ in range(QUOTA)]
    owners: list[int | None] = [None] * len(slots)

    def place(row_index: int, seen: set[int]) -> bool:
        options = all_candidates[row_index]
        for slot, category in sorted(enumerate(slots), key=lambda item: (item[1] not in options, item[0])):
            if slot in seen or category not in options:
                continue
            seen.add(slot)
            owner = owners[slot]
            if owner is None or place(owner, seen):
                owners[slot] = row_index
                return True
        return False

    for row_index in sorted(range(len(all_candidates)), key=lambda index: len(all_candidates[index])):
        if not place(row_index, set()):
            raise ValueError(
                f"cannot assign five balanced mutations for row {row_index}; "
                f"available={sorted(all_candidates[row_index])}"
            )
    assigned = [""] * len(all_candidates)
    for slot, owner in enumerate(owners):
        if owner is not None:
            assigned[owner] = slots[slot]
    if any(not value for value in assigned):
        raise AssertionError("mutation assignment left rows unassigned")
    return assigned


def rename_theorem(formal: str, name: str) -> str:
    return THEOREM_NAME_RE.sub(lambda match: f"{match.group(1)} {name}", formal, count=1)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--true100", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--seed", type=int, default=20260723)
    args = parser.parse_args()

    true_rows = read_jsonl(args.true100)
    if len(true_rows) != 100 or len({row.get("name") for row in true_rows}) != 100:
        raise ValueError("--true100 must contain exactly 100 uniquely named rows")
    all_candidates = [candidates(str(row["formal_statement"]), index) for index, row in enumerate(true_rows)]
    assignments = balanced_assignment(all_candidates)

    false_rows: list[dict[str, Any]] = []
    manifest: list[dict[str, Any]] = []
    for row, options, category in zip(true_rows, all_candidates, assignments, strict=True):
        mutation = options[category]
        source_name = str(row["name"])
        false_name = "false_hard_" + source_name.removeprefix("true_structural_")
        false_rows.append(
            {
                "name": false_name,
                "split": "paired_hard_false100",
                "informal_prefix": row.get("informal_prefix", ""),
                "formal_statement": rename_theorem(mutation.formal_statement, false_name),
                "false_category": mutation.category,
                "false_transform": mutation.transform,
                "false_fix": list(mutation.fix),
                "source_true_name": source_name,
            }
        )
        manifest.append(
            {
                "true_name": source_name,
                "false_name": false_name,
                "false_category": mutation.category,
                "false_transform": mutation.transform,
                "false_fix": list(mutation.fix),
                "changed_fragments": [list(pair) for pair in mutation.changed_fragments],
                "counterexample_status": "paired_incompatibility_pending_external_validation",
            }
        )

    counts = Counter(assignments)
    expected = Counter({category: QUOTA for category in CATEGORIES})
    if counts != expected:
        raise AssertionError(f"unexpected mutation counts: {counts}")
    args.output_dir.mkdir(parents=True, exist_ok=False)
    write_jsonl(args.output_dir / "true100.jsonl", true_rows)
    write_jsonl(args.output_dir / "false100.jsonl", false_rows)
    write_jsonl(args.output_dir / "manifest.jsonl", manifest)
    (args.output_dir / "metadata.json").write_text(
        json.dumps(
            {
                "source_true100": str(args.true100),
                "seed": args.seed,
                "pair_count": 100,
                "category_counts": dict(sorted(counts.items())),
                "public_leakage_policy": "all mutation keys are private",
                "counterexample_certification": "paired_incompatibility_pending_external_validation",
            },
            ensure_ascii=False,
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
