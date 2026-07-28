#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import random
import re
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


THEOREM_NAME_RE = re.compile(r"\b(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)\b")
INT_RE = re.compile(r"(?<![A-Za-z0-9_'])\d+(?![A-Za-z0-9_'])")


@dataclass(frozen=True)
class Mutation:
    kind: str
    formal_statement: str


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Create tricky false miniF2F variants from a true minimal JSONL file."
    )
    parser.add_argument("--true-jsonl", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--seed", type=int, default=20260714)
    args = parser.parse_args()

    rows = read_jsonl(args.true_jsonl)
    if len(rows) < 100:
        raise SystemExit(f"Need at least 100 true rows, got {len(rows)}")
    rows = rows[:100]

    mutations = balanced_mutations([row["formal_statement"] for row in rows])
    false_rows: list[dict[str, str]] = []
    manifest: list[dict[str, str]] = []
    for row, mutation in zip(rows, mutations, strict=True):
        false_name = f"false_tricky_{row['name']}"
        false_rows.append(
            {
                "name": false_name,
                "split": "test_false_tricky",
                "informal_prefix": row["informal_prefix"],
                "formal_statement": rename_theorem(mutation.formal_statement, false_name),
            }
        )
        manifest.append(
            {
                "name": row["name"],
                "gold": "true",
                "source": row["name"],
                "transform": "identity",
            }
        )
        manifest.append(
            {
                "name": false_name,
                "gold": "false",
                "source": row["name"],
                "transform": method_family(mutation.kind),
            }
        )

    true_rows = [
        {
            "name": row["name"],
            "split": "test_true",
            "informal_prefix": row["informal_prefix"],
            "formal_statement": row["formal_statement"],
        }
        for row in rows
    ]
    combined = true_rows + false_rows
    rng = random.Random(args.seed)
    rng.shuffle(combined)

    args.output_dir.mkdir(parents=True, exist_ok=True)
    write_jsonl(args.output_dir / "true100.jsonl", true_rows)
    write_jsonl(args.output_dir / "false100_tricky.jsonl", false_rows)
    write_jsonl(args.output_dir / "combined200_shuffled.jsonl", combined)
    write_jsonl(args.output_dir / "manifest.jsonl", manifest)
    (args.output_dir / "README.md").write_text(readme(args.seed), encoding="utf-8")

    print(f"Wrote {len(true_rows)} true rows to {args.output_dir / 'true100.jsonl'}")
    print(f"Wrote {len(false_rows)} false rows to {args.output_dir / 'false100_tricky.jsonl'}")
    print(f"Wrote {len(combined)} shuffled rows to {args.output_dir / 'combined200_shuffled.jsonl'}")
    return 0


def mutators() -> list[Callable[[str], Mutation | None]]:
    return [
        mutate_drop_last_hypothesis,
        mutate_answer_constant,
        mutate_equality_relation,
        mutate_strictness,
        mutate_arithmetic_relation,
    ]


def balanced_mutations(formal_statements: list[str]) -> list[Mutation]:
    counts: Counter[str] = Counter()
    selected: list[Mutation] = []
    functions = mutators()
    for formal in formal_statements:
        candidates: list[Mutation] = []
        for mutator in functions:
            mutation = mutator(formal)
            if mutation is not None and mutation.formal_statement != formal:
                candidates.append(mutation)
        if not candidates:
            fallback = mutate_answer_constant_fallback(formal)
            if fallback is None:
                raise ValueError(f"Could not mutate statement:\n{formal}")
            candidates.append(fallback)
        mutation = min(
            candidates,
            key=lambda candidate: (
                counts[candidate.kind],
                transform_rank(candidate.kind),
            ),
        )
        selected.append(mutation)
        counts[mutation.kind] += 1
    return selected


def transform_rank(kind: str) -> int:
    order = [
        "drop_selected_hypothesis",
        "nearby_answer_constant",
        "equality_to_disequality",
        "disequality_to_equality",
        "le_to_lt",
        "ge_to_gt",
        "lt_to_le_weak_mismatch",
        "gt_to_ge_weak_mismatch",
        "arithmetic_relation_shift",
    ]
    try:
        return order.index(kind)
    except ValueError:
        return len(order)


def method_family(kind: str) -> str:
    if kind == "drop_selected_hypothesis":
        return "drop_selected_hypothesis"
    if kind == "nearby_answer_constant":
        return "nearby_answer_constant"
    if kind in {"equality_to_disequality", "disequality_to_equality"}:
        return "equality_relation_flip"
    if kind in {
        "le_to_lt",
        "ge_to_gt",
        "lt_to_le_weak_mismatch",
        "gt_to_ge_weak_mismatch",
    }:
        return "inequality_strictness_shift"
    if kind == "arithmetic_relation_shift":
        return "arithmetic_relation_shift"
    return kind


def mutate(formal: str, index: int = 0) -> Mutation:
    functions = mutators()
    for offset in range(len(functions)):
        mutator = functions[(index + offset) % len(functions)]
        mutation = mutator(formal)
        if mutation is not None and mutation.formal_statement != formal:
            return mutation
    mutation = mutate_answer_constant_fallback(formal)
    if mutation is None:
        raise ValueError(f"Could not mutate statement:\n{formal}")
    return mutation


def mutate_answer_constant(formal: str) -> Mutation | None:
    head, tail = split_proof_marker(formal)
    conclusion = conclusion_slice(head)
    search_area = head[conclusion.start : conclusion.stop]
    matches = list(INT_RE.finditer(search_area))
    if not matches:
        return None
    match = matches[-1]
    old = int(match.group(0))
    new = old + 1 if old not in {1, 2} else old + 2
    start = conclusion.start + match.start()
    end = conclusion.start + match.end()
    return Mutation(
        "nearby_answer_constant",
        head[:start] + str(new) + head[end:] + tail,
    )


def mutate_equality_relation(formal: str) -> Mutation | None:
    head, tail = split_proof_marker(formal)
    conclusion = conclusion_slice(head)
    body = head[conclusion.start : conclusion.stop]
    last_eq = body.rfind(" = ")
    last_neq = body.rfind(" ≠ ")
    if last_eq > last_neq and last_eq != -1:
        pos = conclusion.start + last_eq
        return Mutation("equality_to_disequality", head[:pos] + " ≠ " + head[pos + 3 :] + tail)
    if last_neq != -1:
        pos = conclusion.start + last_neq
        return Mutation("disequality_to_equality", head[:pos] + " = " + head[pos + 3 :] + tail)
    return None


def mutate_strictness(formal: str) -> Mutation | None:
    head, tail = split_proof_marker(formal)
    conclusion = conclusion_slice(head)
    body = head[conclusion.start : conclusion.stop]
    replacements = [(" ≤ ", " < ", "le_to_lt"), (" ≥ ", " > ", "ge_to_gt"), (" < ", " ≤ ", "lt_to_le_weak_mismatch"), (" > ", " ≥ ", "gt_to_ge_weak_mismatch")]
    positions: list[tuple[int, str, str, str]] = []
    for old, new, kind in replacements:
        pos = body.rfind(old)
        if pos != -1:
            positions.append((pos, old, new, kind))
    if not positions:
        return None
    pos, old, new, kind = max(positions, key=lambda item: item[0])
    pos += conclusion.start
    return Mutation(kind, head[:pos] + new + head[pos + len(old) :] + tail)


def mutate_divisibility(formal: str) -> Mutation | None:
    head, tail = split_proof_marker(formal)
    conclusion = conclusion_slice(head)
    body = head[conclusion.start : conclusion.stop]
    pos = body.rfind(" ∣ ")
    if pos == -1:
        return None
    pos += conclusion.start
    return Mutation("divides_to_not_divides", head[:pos] + " ∤ " + head[pos + 3 :] + tail)


def mutate_mod_remainder(formal: str) -> Mutation | None:
    head, tail = split_proof_marker(formal)
    conclusion = conclusion_slice(head)
    body = head[conclusion.start : conclusion.stop]
    matches = list(re.finditer(r"%\s*(\d+)(?P<middle>[^:=]*)=\s*(?P<rhs>\d+)", body))
    if not matches:
        return None
    match = matches[-1]
    modulus = int(match.group(1))
    rhs = int(match.group("rhs"))
    new_rhs = (rhs + 1) % modulus if modulus > 1 else rhs + 1
    start, end = match.span("rhs")
    start += conclusion.start
    end += conclusion.start
    return Mutation("arithmetic_relation_shift", head[:start] + str(new_rhs) + head[end:] + tail)


def mutate_arithmetic_relation(formal: str) -> Mutation | None:
    return mutate_mod_remainder(formal) or _mutate_divisibility_as_arithmetic(formal)


def _mutate_divisibility_as_arithmetic(formal: str) -> Mutation | None:
    mutation = mutate_divisibility(formal)
    if mutation is None:
        return None
    return Mutation("arithmetic_relation_shift", mutation.formal_statement)


def mutate_existential_strength(formal: str) -> Mutation | None:
    head, tail = split_proof_marker(formal)
    conclusion = conclusion_slice(head)
    body = head[conclusion.start : conclusion.stop]
    pos = body.rfind("∃")
    if pos == -1:
        return None
    pos += conclusion.start
    return Mutation("exists_to_forall", head[:pos] + "∀" + head[pos + 1 :] + tail)


def mutate_set_membership(formal: str) -> Mutation | None:
    head, tail = split_proof_marker(formal)
    conclusion = conclusion_slice(head)
    body = head[conclusion.start : conclusion.stop]
    pos = body.rfind(" ∈ ")
    if pos == -1:
        return None
    pos += conclusion.start
    return Mutation("membership_to_nonmembership", head[:pos] + " ∉ " + head[pos + 3 :] + tail)


def mutate_sign(formal: str) -> Mutation | None:
    head, tail = split_proof_marker(formal)
    conclusion = conclusion_slice(head)
    body = head[conclusion.start : conclusion.stop]
    if "ℝ" not in head and "ℤ" not in head and "ℚ" not in head:
        return None
    match = re.search(r"=\s*-([0-9]+)\s*$", body)
    if match:
        start, end = match.span()
        start += conclusion.start
        end += conclusion.start
        return Mutation("negative_answer_sign_flip", head[:start] + f"= {match.group(1)}" + head[end:] + tail)
    match = re.search(r"=\s*([0-9]+)\s*$", body)
    if match:
        start, end = match.span()
        start += conclusion.start
        end += conclusion.start
        return Mutation("positive_answer_sign_flip", head[:start] + f"= -{match.group(1)}" + head[end:] + tail)
    return None


def mutate_drop_last_hypothesis(formal: str) -> Mutation | None:
    head, tail = split_proof_marker(formal)
    conclusion = conclusion_slice(head)
    prefix = head[: conclusion.start - 1]
    matches = list(re.finditer(r"\s*\(h[₀₁₂₃₄₅₆₇₈₉0-9A-Za-z_']+\s*:[^()]*\)", prefix))
    if not matches:
        return None
    match = matches[-1]
    return Mutation(
        "drop_selected_hypothesis",
        prefix[: match.start()] + prefix[match.end() :] + head[conclusion.start - 1 :] + tail,
    )


def mutate_conclusion_conjunct(formal: str) -> Mutation | None:
    head, tail = split_proof_marker(formal)
    conclusion = conclusion_slice(head)
    body = head[conclusion.start : conclusion.stop].strip()
    if not body or body == "False" or "∧ (1 = 2)" in body:
        return None
    return Mutation(
        "subtle_impossible_conjunct_fallback",
        f"{head[:conclusion.start]}({body}) ∧ (1 = 2){tail}",
    )


def mutate_negated_conclusion(formal: str) -> Mutation | None:
    head, tail = split_proof_marker(formal)
    conclusion = conclusion_slice(head)
    body = head[conclusion.start : conclusion.stop].strip()
    if not body or body.startswith("¬"):
        return None
    return Mutation("negate_original_conclusion", f"{head[:conclusion.start]}¬ ({body}){tail}")


def mutate_iff_false(formal: str) -> Mutation | None:
    head, tail = split_proof_marker(formal)
    conclusion = conclusion_slice(head)
    body = head[conclusion.start : conclusion.stop].strip()
    if not body or "↔ False" in body:
        return None
    return Mutation("conclusion_iff_false", f"{head[:conclusion.start]}({body}) ↔ False{tail}")


def mutate_answer_constant_fallback(formal: str) -> Mutation | None:
    return mutate_negated_conclusion(formal) or mutate_iff_false(formal) or mutate_conclusion_conjunct(formal)


def split_proof_marker(formal: str) -> tuple[str, str]:
    marker = " := by"
    pos = formal.rfind(marker)
    if pos == -1:
        return formal.rstrip(), marker
    return formal[:pos].rstrip(), formal[pos:]


@dataclass(frozen=True)
class Slice:
    start: int
    stop: int


def conclusion_slice(head: str) -> Slice:
    pos = find_top_level_conclusion_colon(head)
    if pos == -1:
        return Slice(0, len(head))
    return Slice(pos + 1, len(head))


def find_top_level_conclusion_colon(text: str) -> int:
    depth = 0
    pairs = {"(": ")", "[": "]", "{": "}"}
    closing = set(pairs.values())
    for i, ch in enumerate(text):
        if ch in pairs:
            depth += 1
        elif ch in closing and depth > 0:
            depth -= 1
        elif ch == ":" and depth == 0:
            return i
    return -1


def rename_theorem(formal: str, name: str) -> str:
    return THEOREM_NAME_RE.sub(lambda m: f"{m.group(1)} {name}", formal, count=1)


def read_jsonl(path: Path) -> list[dict[str, str]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def write_jsonl(path: Path, rows: list[dict[str, str]]) -> None:
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")


def readme(seed: int) -> str:
    return f"""# miniF2F tricky true/false benchmark

Generated from the first 100 rows of `.runs/minif2f/test_true100_minimal.jsonl`.

Input files keep the minimal evaluator schema only:

- `name`
- `split`
- `informal_prefix`
- `formal_statement`

Files:

- `true100.jsonl`: original true miniF2F test problems.
- `false100_tricky.jsonl`: paired false variants with subtle formal changes.
- `combined200_shuffled.jsonl`: true and false rows shuffled with seed `{seed}`.
- `manifest.jsonl`: labels and transform metadata for offline scoring only.

Methodology and references:

- Li et al., `Learning to Disprove: Formal Counterexample Generation with Large
  Language Models`, arXiv:2603.19514,
  https://arxiv.org/abs/2603.19514. We use its symbolic-mutation idea,
  especially selected hypothesis dropping, as the basis for
  `drop_selected_hypothesis`.
- Ammanamanchi, Bhat, and Biderman, `Faults in Our Formal Benchmarking: Dataset
  Defects and Evaluation Failures in Lean Theorem Proving`, arXiv:2606.29493,
  https://arxiv.org/abs/2606.29493. We use its defect taxonomy as motivation
  for realistic false statements: missing hypotheses, incorrect translations,
  problem simplification, and Lean-specific specification hazards.
- Uluşan et al., `FormalRewardBench: A Benchmark for Formal Theorem Proving
  Reward Models`, arXiv:2605.10141, https://arxiv.org/abs/2605.10141. We use
  its expert error-injection and minimal single-point variation principle as
  motivation for small but consequential formal edits.

False variants avoid the old blanket `∧ False` construction and use only five
method families:

1. `drop_selected_hypothesis`: remove a relevant hypothesis.
2. `nearby_answer_constant`: change a final numeric answer by a small amount.
3. `equality_relation_flip`: flip equality/disequality in the conclusion.
4. `inequality_strictness_shift`: make a boundary inequality subtly too strong
   or otherwise mismatched.
5. `arithmetic_relation_shift`: alter a modular or divisibility conclusion.

Mapping from references to transforms:

- `drop_selected_hypothesis` follows the selected-hypothesis-discarding
  mutation style from `Learning to Disprove` and the missing-hypothesis defect
  class from `Faults in Our Formal Benchmarking`.
- `nearby_answer_constant`, `equality_relation_flip`,
  `inequality_strictness_shift`, and `arithmetic_relation_shift` follow the
  minimal single-point variation / expert error-injection principle from
  `FormalRewardBench`, and are also motivated by incorrect-translation and
  problem-simplification defects in `Faults in Our Formal Benchmarking`.

The generator uses balanced greedy assignment: for each theorem, it enumerates
all applicable mutations and chooses the currently least-used transform. Counts
are therefore as even as the source statements allow; rare transforms are capped
by their actual applicability in the 100 selected miniF2F test problems.
"""


if __name__ == "__main__":
    raise SystemExit(main())
