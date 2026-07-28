#!/usr/bin/env python3
"""Mutate an established true100 into five balanced false categories."""

from __future__ import annotations

import argparse
import json
import random
import re
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any


CATEGORIES = (
    "relation_weakening",
    "connection_definition_removal",
    "discrete_condition_removal",
    "branch_range_removal",
    "structure_uniqueness_removal",
)
QUOTA = 20
THEOREM_NAME_RE = re.compile(
    r"\b(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
DISCRETE_TOKENS = (
    "%",
    "∣",
    "∤",
    "[MOD",
    "Even",
    "Odd",
    "Prime",
    "Nat.digits",
    "Nat.divisors",
    "Nat.ofDigits",
)
STRUCTURE_TOKENS = (
    "∀",
    "∃",
    "↔",
    "IsLeast",
    "Function.",
    "Injective",
    "Surjective",
    "Bijective",
    "Pairwise",
    "IsSquare",
    "⁻¹'",
    "Set",
    "Finset",
)
KNOWN_FORMAL_REPAIRS = {
    "true_structural_minif2f_valid_amc12b_2003_p6": (
        "theorem true_structural_minif2f_valid_amc12b_2003_p6 "
        "(a r : ℝ) (u : ℕ → ℝ) (h₀ : ∀ k, u k = a * r ^ k) (h₁ : u 1 = 2)\n"
        "    (h₂ : u 3 = 6) : let a := answer(2 / Real.sqrt 3); "
        "u 0 = a ∨ u 0 = -a := by"
    ),
}
STRUCTURAL_EQUATION_SOURCES = {
    "true_structural_minif2f_amc12b_2021_p3",
    "true_structural_minif2f_mathd_algebra_209",
    "true_structural_minif2f_mathd_algebra_459",
    "true_structural_minif2f_algebra_sqineq_unitcircatbpabsamblt1",
    "true_structural_minif2f_mathd_algebra_188",
    "true_structural_minif2f_mathd_algebra_107",
}
DISCRETE_EQUATION_SOURCES = {
    "true_structural_minif2f_mathd_numbertheory_483",
    "true_structural_minif2f_valid_algebra_xmysqpymzsqpzmxsqeqxyz_xpypzp6dvdx3y3z3",
    "true_structural_minif2f_valid_amc12b_2004_p3",
    "true_structural_minif2f_valid_mathd_numbertheory_136",
    "true_structural_minif2f_valid_mathd_numbertheory_48",
}
CATEGORY_OVERRIDES = {
    # Positivity/range hypotheses below are redundant; mutate an essential relation instead.
    "true_structural_minif2f_mathd_algebra_478": "relation_weakening",
    "true_structural_minif2f_aime_1983_p1": "connection_definition_removal",
    "true_structural_minif2f_mathd_algebra_398": "relation_weakening",
    "true_structural_minif2f_algebra_apbmpcneq0_aeq0anbeq0anceq0": "relation_weakening",
    "true_structural_minif2f_amc12b_2002_p7": "relation_weakening",
    "true_structural_minif2f_valid_aime_1984_p5": "connection_definition_removal",
    "true_structural_minif2f_valid_mathd_numbertheory_48": "relation_weakening",
    "true_structural_minif2f_mathd_algebra_392": "relation_weakening",
    "true_structural_minif2f_valid_aime_1991_p1": "connection_definition_removal",
    "true_structural_minif2f_valid_mathd_algebra_96": "connection_definition_removal",
    "true_structural_minif2f_valid_amc12b_2003_p17": "relation_weakening",
    "true_structural_minif2f_valid_numbertheory_xsqpysqintdenomeq": "connection_definition_removal",
    "true_structural_minif2f_mathd_numbertheory_430": "connection_definition_removal",
    "true_structural_minif2f_mathd_algebra_80": "connection_definition_removal",
    # Exact discrete constraints and domain exclusions replace those ten range slots.
    "true_structural_minif2f_valid_imo_1978_p5": "branch_range_removal",
    "true_structural_minif2f_valid_amc12_2001_p2": "branch_range_removal",
    "true_structural_minif2f_valid_mathd_numbertheory_284": "branch_range_removal",
    "true_structural_minif2f_mathd_numbertheory_1124": "branch_range_removal",
    "true_structural_minif2f_mathd_numbertheory_293": "branch_range_removal",
    "true_structural_minif2f_valid_mathd_numbertheory_257": "branch_range_removal",
    "true_structural_minif2f_mathd_algebra_33": "branch_range_removal",
    "true_structural_minif2f_mathd_algebra_487": "branch_range_removal",
    "true_structural_minif2f_valid_mathd_algebra_73": "branch_range_removal",
    "true_structural_minif2f_valid_amc12a_2013_p8": "branch_range_removal",
    "true_structural_minif2f_valid_mathd_numbertheory_780": "branch_range_removal",
    "true_structural_minif2f_imo_1969_p2": "branch_range_removal",
    # Preserve all category capacities after moving the domain exclusions.
    "true_structural_minif2f_mathd_algebra_209": "structure_uniqueness_removal",
    "true_structural_minif2f_algebra_sqineq_unitcircatbpabsamblt1": "structure_uniqueness_removal",
    "true_structural_minif2f_mathd_algebra_188": "structure_uniqueness_removal",
    "true_structural_minif2f_mathd_algebra_107": "structure_uniqueness_removal",
    "true_structural_minif2f_amc12b_2021_p3": "structure_uniqueness_removal",
    "true_structural_minif2f_mathd_algebra_459": "structure_uniqueness_removal",
    "true_structural_minif2f_valid_imo_1978_p5": "structure_uniqueness_removal",
    "true_structural_minif2f_valid_mathd_algebra_131": "structure_uniqueness_removal",
    "true_structural_minif2f_mathd_numbertheory_483": "discrete_condition_removal",
    "true_structural_minif2f_valid_mathd_numbertheory_48": "discrete_condition_removal",
    "true_structural_minif2f_valid_algebra_xmysqpymzsqpzmxsqeqxyz_xpypzp6dvdx3y3z3": "discrete_condition_removal",
    "true_structural_minif2f_valid_amc12b_2004_p3": "discrete_condition_removal",
    "true_structural_minif2f_valid_mathd_numbertheory_136": "discrete_condition_removal",
}
PREFERRED_TRANSFORM_TEXT = {
    "true_structural_minif2f_valid_amc12_2001_p2": "(h₀ :",
    "true_structural_minif2f_valid_amc12a_2017_p7": "(h₂ :",
}


@dataclass(frozen=True)
class Param:
    start: int
    stop: int
    text: str
    prop: str


@dataclass(frozen=True)
class Candidate:
    category: str
    formal_statement: str
    transform: str
    fix: str
    score: int


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--true100", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--seed", type=int, default=20260720)
    return parser.parse_args()


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")


def top_level_paren_spans(text: str) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    depth = 0
    start: int | None = None
    for index, char in enumerate(text):
        if char == "(":
            if depth == 0:
                start = index
            depth += 1
        elif char == ")" and depth:
            depth -= 1
            if depth == 0 and start is not None:
                spans.append((start, index + 1))
                start = None
    return spans


def find_conclusion_colon(text: str) -> int:
    depth = 0
    for index, char in enumerate(text):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        elif char == ":" and depth == 0:
            return index
    return -1


def split_proof(formal: str) -> tuple[str, str]:
    position = formal.rfind(" := by")
    return (formal.rstrip(), " := by") if position < 0 else (formal[:position].rstrip(), formal[position:])


def hypothesis_params(formal: str) -> list[Param]:
    head, _ = split_proof(formal)
    conclusion = find_conclusion_colon(head)
    prefix = head if conclusion < 0 else head[:conclusion]
    params: list[Param] = []
    for start, stop in top_level_paren_spans(prefix):
        text = prefix[start:stop]
        inner = text[1:-1].strip()
        if ":" not in inner:
            continue
        names, prop = inner.split(":", 1)
        identifiers = names.split()
        if identifiers and all(name.startswith("h") for name in identifiers):
            params.append(Param(start, stop, text, prop.strip()))
    return params


def conclusion(formal: str) -> str:
    head, _ = split_proof(formal)
    position = find_conclusion_colon(head)
    return head[position + 1 :].strip() if position >= 0 else ""


def replace_param(formal: str, param: Param, replacement: str) -> str:
    value = formal[: param.start] + replacement + formal[param.stop :]
    return re.sub(r"[ \t]{2,}", " ", value).strip()


def drop_candidate(formal: str, param: Param, category: str, score: int) -> Candidate:
    removed = param.text.strip()
    return Candidate(
        category=category,
        formal_statement=replace_param(formal, param, ""),
        transform=f"dropped hypothesis `{removed}`",
        fix=f"add the missing hypothesis `{removed}`",
        score=score,
    )


def is_numeric_equality(prop: str) -> bool:
    blocked = ("↔", "∀", "∃", "Set", "Finset", "Function", "Pairwise", "ℂ", "Complex")
    return " = " in prop and not any(token in prop for token in blocked)


def candidates(formal: str, source_name: str = "") -> dict[str, list[Candidate]]:
    result = {category: [] for category in CATEGORIES}
    target = conclusion(formal)
    for index, param in enumerate(hypothesis_params(formal)):
        prop = param.prop
        base_score = min(len(prop), 100) + index
        if any(token in prop for token in DISCRETE_TOKENS):
            result["discrete_condition_removal"].append(
                drop_candidate(formal, param, "discrete_condition_removal", base_score + 80)
            )
        has_order = any(token in prop for token in ("<", "≤", ">", "≥", "≠"))
        if has_order and not any(token in prop for token in DISCRETE_TOKENS):
            result["branch_range_removal"].append(
                drop_candidate(formal, param, "branch_range_removal", base_score + 40)
            )
        structural = any(token in prop for token in STRUCTURE_TOKENS) or "≠" in prop
        if structural and not any(token in prop for token in DISCRETE_TOKENS):
            result["structure_uniqueness_removal"].append(
                drop_candidate(formal, param, "structure_uniqueness_removal", base_score + 60)
            )
        if source_name in DISCRETE_EQUATION_SOURCES and "∀" in prop:
            result["discrete_condition_removal"].append(
                drop_candidate(
                    formal,
                    param,
                    "discrete_condition_removal",
                    base_score + 70,
                )
            )
        if is_numeric_equality(prop):
            direct_penalty = -100 if prop.strip() == target else 0
            result["connection_definition_removal"].append(
                drop_candidate(
                    formal,
                    param,
                    "connection_definition_removal",
                    base_score + direct_penalty,
                )
            )
            equality = prop.rfind(" = ")
            weakened = prop[:equality] + " ≤ " + prop[equality + 3 :]
            replacement = param.text.replace(prop, weakened, 1)
            result["relation_weakening"].append(
                Candidate(
                    category="relation_weakening",
                    formal_statement=replace_param(formal, param, replacement),
                    transform=f"weakened hypothesis `{prop}` to `{weakened}`",
                    fix=f"replace `{weakened}` with `{prop}`",
                    score=base_score + direct_penalty,
                )
            )
            if source_name in STRUCTURAL_EQUATION_SOURCES:
                result["structure_uniqueness_removal"].append(
                    drop_candidate(
                        formal,
                        param,
                        "structure_uniqueness_removal",
                        base_score + direct_penalty,
                    )
                )
            if source_name in DISCRETE_EQUATION_SOURCES:
                result["discrete_condition_removal"].append(
                    drop_candidate(
                        formal,
                        param,
                        "discrete_condition_removal",
                        base_score + direct_penalty,
                    )
                )
    for values in result.values():
        values.sort(key=lambda item: item.score, reverse=True)
    return {key: value for key, value in result.items() if value}


def assign_categories(
    all_candidates: list[dict[str, list[Candidate]]], source_names: list[str]
) -> list[str]:
    fixed = {
        index: CATEGORY_OVERRIDES[name]
        for index, name in enumerate(source_names)
        if name in CATEGORY_OVERRIDES
    }
    fixed_counts = Counter(fixed.values())
    slots = [
        category
        for category in CATEGORIES
        for _ in range(QUOTA - fixed_counts[category])
    ]
    slot_owner: list[int | None] = [None] * len(slots)

    def place(row_index: int, seen: set[int]) -> bool:
        options = all_candidates[row_index]
        slot_order = sorted(
            range(len(slots)),
            key=lambda slot: (
                slots[slot] not in options,
                len(options.get(slots[slot], ())),
                slot,
            ),
        )
        for slot in slot_order:
            if slot in seen or slots[slot] not in options:
                continue
            seen.add(slot)
            owner = slot_owner[slot]
            if owner is None or place(owner, seen):
                slot_owner[slot] = row_index
                return True
        return False

    order = sorted(
        (index for index in range(len(all_candidates)) if index not in fixed),
        key=lambda index: (len(all_candidates[index]), index),
    )
    for row_index in order:
        if not place(row_index, set()):
            available = sorted(all_candidates[row_index])
            raise ValueError(f"cannot satisfy 20-per-category assignment at row {row_index}: {available}")
    assigned = [fixed.get(index, "") for index in range(len(all_candidates))]
    for slot, owner in enumerate(slot_owner):
        if owner is not None:
            assigned[owner] = slots[slot]
    if any(not category for category in assigned):
        raise AssertionError("category assignment left rows unassigned")
    return assigned


def rename_theorem(formal: str, name: str) -> str:
    return THEOREM_NAME_RE.sub(lambda match: f"{match.group(1)} {name}", formal, count=1)


def neutral_name(true_name: str) -> str:
    base = true_name.removeprefix("true_structural_")
    return f"paired_variant_{base}"


def repair_known_formal_statement(row: dict[str, Any]) -> dict[str, Any]:
    repaired = dict(row)
    replacement = KNOWN_FORMAL_REPAIRS.get(str(row.get("name")))
    if replacement is not None:
        repaired["formal_statement"] = replacement
        repaired["formal_repair"] = "restored truncated conclusion from MiniF2F/Valid.lean"
    return repaired


def main() -> None:
    args = parse_args()
    true_rows = [repair_known_formal_statement(row) for row in read_jsonl(args.true100)]
    if len(true_rows) != 100 or len({row.get("name") for row in true_rows}) != 100:
        raise ValueError("--true100 must contain exactly 100 uniquely named rows")

    candidate_sets = [
        candidates(str(row["formal_statement"]), str(row["name"])) for row in true_rows
    ]
    assignments = assign_categories(
        candidate_sets, [str(row["name"]) for row in true_rows]
    )
    rng = random.Random(args.seed)
    false_rows: list[dict[str, Any]] = []
    manifest: list[dict[str, Any]] = []
    for true_row, options, category in zip(true_rows, candidate_sets, assignments, strict=True):
        best_score = options[category][0].score
        preferred_text = PREFERRED_TRANSFORM_TEXT.get(str(true_row["name"]))
        eligible = options[category]
        if preferred_text is not None:
            eligible = [
                candidate for candidate in eligible if preferred_text in candidate.transform
            ]
            if not eligible:
                raise ValueError(
                    f"preferred transform {preferred_text!r} unavailable for {true_row['name']}"
                )
            best_score = eligible[0].score
        tied = [candidate for candidate in eligible if candidate.score == best_score]
        mutation = rng.choice(tied)
        false_name = neutral_name(str(true_row["name"]))
        false_rows.append(
            {
                "name": false_name,
                "split": "paired_false100_five_types",
                "informal_prefix": true_row.get("informal_prefix", ""),
                "formal_statement": rename_theorem(mutation.formal_statement, false_name),
                "false_category": category,
                "false_transform": mutation.transform,
                "false_fix": [mutation.fix],
                "source_true_name": true_row["name"],
            }
        )
        manifest.append(
            {
                "true_name": true_row["name"],
                "false_name": false_name,
                "false_category": category,
                "false_transform": mutation.transform,
                "false_fix": [mutation.fix],
                "counterexample_status": "pending",
            }
        )

    counts = Counter(assignments)
    if counts != Counter({category: QUOTA for category in CATEGORIES}):
        raise AssertionError(f"unexpected category counts: {counts}")

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
                "counterexample_certification": "pending",
                "source_repairs": [
                    row["name"] for row in true_rows if row.get("formal_repair")
                ],
            },
            ensure_ascii=False,
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    print(json.dumps(dict(sorted(counts.items())), indent=2))


if __name__ == "__main__":
    main()
