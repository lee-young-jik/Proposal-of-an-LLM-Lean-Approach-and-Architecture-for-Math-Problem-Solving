#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import random
import re
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


THEOREM_NAME_RE = re.compile(r"\b(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b")
DESIRED_QUOTAS = {
    "drop_mod_or_divisibility_hypothesis": 20,
    "drop_branch_or_bound_hypothesis": 10,
    "drop_equational_hypothesis": 40,
    "weaken_hypothesis_equality_to_le": 30,
}


@dataclass(frozen=True)
class Mutation:
    kind: str
    formal_statement: str
    false_transform: str
    false_fix: tuple[str, ...]


@dataclass(frozen=True)
class Param:
    start: int
    stop: int
    text: str
    names: tuple[str, ...]
    prop: str


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Build a miniF2F true100 plus structurally ambiguous false100 set. "
            "False transforms prioritize missing hypotheses and weakened hypotheses, "
            "not answer-constant flips."
        )
    )
    parser.add_argument("--input", type=Path, action="append", required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--limit", type=int, default=100)
    parser.add_argument("--seed", type=int, default=20260715)
    args = parser.parse_args()

    rows = dedupe_by_name(row for path in args.input for row in read_jsonl(path))
    selected: list[tuple[dict[str, str], Mutation]] = []
    counts: Counter[str] = Counter()
    selected_names: set[str] = set()
    for allow_generic in (False, True):
        for row in rows:
            if row["name"] in selected_names:
                continue
            formal = row["formal_statement"]
            candidates = structural_mutations(formal)
            if not allow_generic:
                candidates = [item for item in candidates if item.kind != "drop_selected_hypothesis"]
            if not candidates:
                continue
            under_quota = [
                item
                for item in candidates
                if counts[item.kind] < DESIRED_QUOTAS.get(item.kind, 0)
            ]
            pool = under_quota or candidates
            mutation = min(pool, key=lambda item: (transform_rank(item.kind), counts[item.kind]))
            counts[mutation.kind] += 1
            selected.append((row, mutation))
            selected_names.add(row["name"])
            if len(selected) >= args.limit:
                break
        if len(selected) >= args.limit:
            break

    if len(selected) < args.limit:
        raise SystemExit(f"Only found {len(selected)} structural mutation candidates, need {args.limit}")

    true_rows: list[dict[str, str]] = []
    false_rows: list[dict[str, object]] = []
    manifest: list[dict[str, object]] = []
    for row, mutation in selected:
        true_name = f"true_structural_{row['name']}"
        false_name = f"false_structural_{row['name']}"
        true_rows.append(
            {
                "name": true_name,
                "split": "test_true_structural_100",
                "informal_prefix": row["informal_prefix"],
                "formal_statement": rename_theorem(row["formal_statement"], true_name),
            }
        )
        false_rows.append(
            {
                "name": false_name,
                "split": "test_false_structural_100",
                "informal_prefix": structural_informal(row["informal_prefix"]),
                "formal_statement": rename_theorem(mutation.formal_statement, false_name),
                "false_transform": mutation.false_transform,
                "false_fix": list(mutation.false_fix),
            }
        )
        manifest.append(
            {
                "true_name": true_name,
                "false_name": false_name,
                "source_name": row["name"],
                "transform_kind": mutation.kind,
                "false_transform": mutation.false_transform,
                "false_fix": list(mutation.false_fix),
            }
        )

    combined = true_rows + false_rows
    random.Random(args.seed).shuffle(combined)

    args.output_dir.mkdir(parents=True, exist_ok=True)
    write_jsonl(args.output_dir / "true100.jsonl", true_rows)
    write_jsonl(args.output_dir / "false100_structural.jsonl", false_rows)
    write_jsonl(args.output_dir / "combined200_shuffled.jsonl", combined)
    write_jsonl(args.output_dir / "manifest.jsonl", manifest)
    (args.output_dir / "README.md").write_text(readme(counts, args.seed), encoding="utf-8")

    print(f"Wrote {len(true_rows)} true rows to {args.output_dir / 'true100.jsonl'}")
    print(f"Wrote {len(false_rows)} false rows to {args.output_dir / 'false100_structural.jsonl'}")
    print(f"Wrote {len(combined)} shuffled rows to {args.output_dir / 'combined200_shuffled.jsonl'}")
    print("Transform counts:")
    for key, value in counts.most_common():
        print(f"  {key}: {value}")
    return 0


def structural_mutations(formal: str) -> list[Mutation]:
    mutators = [
        mutate_drop_mod_or_divisibility_hypothesis,
        mutate_drop_branch_hypothesis,
        mutate_weaken_hypothesis_equality,
        mutate_drop_equational_hypothesis,
        mutate_drop_any_hypothesis,
    ]
    mutations: list[Mutation] = []
    seen: set[str] = set()
    for mutator in mutators:
        mutation = mutator(formal)
        if mutation and mutation.formal_statement != formal and mutation.formal_statement not in seen:
            mutations.append(mutation)
            seen.add(mutation.formal_statement)
    return mutations


def mutate_drop_mod_or_divisibility_hypothesis(formal: str) -> Mutation | None:
    for param in reversed(hypothesis_params(formal)):
        if any(token in param.prop for token in ("%", "[MOD", "∣", "∤")):
            return drop_param_mutation(formal, param, "drop_mod_or_divisibility_hypothesis")
    return None


def mutate_drop_branch_hypothesis(formal: str) -> Mutation | None:
    if "abs" not in formal and "ite" not in formal and "if " not in formal:
        return None
    for param in reversed(hypothesis_params(formal)):
        prop = param.prop
        has_order = any(token in prop for token in ("<", "≤", ">", "≥"))
        has_eq = " = " in prop
        if has_order and not has_eq:
            return drop_param_mutation(formal, param, "drop_branch_or_bound_hypothesis")
    return None


def mutate_weaken_hypothesis_equality(formal: str) -> Mutation | None:
    if "ℂ" in formal or "Prop" in formal:
        return None
    for param in reversed(hypothesis_params(formal)):
        prop = param.prop
        if not is_numeric_hypothesis(prop):
            continue
        eq_pos = prop.rfind(" = ")
        if eq_pos == -1:
            continue
        old_prop = prop
        new_prop = prop[:eq_pos] + " ≤ " + prop[eq_pos + 3 :]
        new_param = param.text.replace(old_prop, new_prop, 1)
        mutated = formal[: param.start] + new_param + formal[param.stop :]
        return Mutation(
            "weaken_hypothesis_equality_to_le",
            mutated,
            f"weakened hypothesis `{old_prop}` to `{new_prop}`",
            (f"replace `{new_prop}` with `{old_prop}`",),
        )
    return None


def mutate_drop_equational_hypothesis(formal: str) -> Mutation | None:
    for param in reversed(hypothesis_params(formal)):
        if is_numeric_hypothesis(param.prop) and " = " in param.prop:
            return drop_param_mutation(formal, param, "drop_equational_hypothesis")
    return None


def mutate_drop_any_hypothesis(formal: str) -> Mutation | None:
    params = hypothesis_params(formal)
    if not params:
        return None
    return drop_param_mutation(formal, params[-1], "drop_selected_hypothesis")


def drop_param_mutation(formal: str, param: Param, kind: str) -> Mutation:
    removed = param.text.strip()
    mutated = formal[: param.start] + formal[param.stop :]
    return Mutation(
        kind,
        normalize_spaces_around_params(mutated),
        f"dropped hypothesis `{removed}`",
        (f"add the missing hypothesis `{removed}`",),
    )


def hypothesis_params(formal: str) -> list[Param]:
    head, _ = split_proof_marker(formal)
    conclusion = conclusion_slice(head)
    prefix = head[: max(0, conclusion.start - 1)]
    params: list[Param] = []
    for start, stop in top_level_paren_spans(prefix):
        text = prefix[start:stop]
        inner = text[1:-1].strip()
        if ":" not in inner:
            continue
        left, prop = inner.split(":", 1)
        names = tuple(part.strip() for part in left.split() if part.strip())
        if not names or not all(name.startswith("h") for name in names):
            continue
        params.append(Param(start=start, stop=stop, text=text, names=names, prop=prop.strip()))
    return params


def top_level_paren_spans(text: str) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    depth = 0
    start: int | None = None
    for index, char in enumerate(text):
        if char == "(":
            if depth == 0:
                start = index
            depth += 1
        elif char == ")":
            if depth:
                depth -= 1
                if depth == 0 and start is not None:
                    spans.append((start, index + 1))
                    start = None
    return spans


def is_numeric_hypothesis(prop: str) -> bool:
    blocked = ("↔", "∀", "∃", "Set", "Finset", "Polynomial", "Matrix", "Equiv", "Function")
    if any(token in prop for token in blocked):
        return False
    if any(token in prop for token in ("ℂ", "Complex")):
        return False
    return any(token in prop for token in ("=", "<", "≤", ">", "≥", "%", "∣"))


def transform_rank(kind: str) -> int:
    order = [
        "drop_mod_or_divisibility_hypothesis",
        "drop_branch_or_bound_hypothesis",
        "drop_equational_hypothesis",
        "weaken_hypothesis_equality_to_le",
        "drop_selected_hypothesis",
    ]
    try:
        return order.index(kind)
    except ValueError:
        return len(order)


def structural_informal(informal: str) -> str:
    text = informal.strip() or "Solve the formal miniF2F target below."
    return (
        f"Original miniF2F problem: {text}\n\n"
        "The Lean formal target below is authoritative for this run and may have a missing "
        "or weakened hypothesis. Decide whether the formal target follows; if not, identify "
        "exactly what must be restored to make it true."
    )


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
    return THEOREM_NAME_RE.sub(lambda match: f"{match.group(1)} {name}", formal, count=1)


def normalize_spaces_around_params(formal: str) -> str:
    return re.sub(r"\s{2,}", " ", formal).replace(" : ", " : ").strip()


def dedupe_by_name(rows: Iterable[dict[str, str]]) -> list[dict[str, str]]:
    seen: set[str] = set()
    unique: list[dict[str, str]] = []
    for row in rows:
        name = str(row.get("name", ""))
        if not name or name in seen:
            continue
        seen.add(name)
        unique.append(row)
    return unique


def read_jsonl(path: Path) -> list[dict[str, str]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def write_jsonl(path: Path, rows: list[dict[str, object]]) -> None:
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")


def readme(counts: Counter[str], seed: int) -> str:
    lines = [
        "# miniF2F structural false100",
        "",
        "This dataset is designed after the 5-problem structural false experiment where",
        "the dual pipeline found false corrections in fewer rounds/trials than the single",
        "pipeline on missing congruence and missing branch-condition cases.",
        "",
        "Files:",
        "",
        "- `true100.jsonl`: 100 selected true miniF2F statements.",
        "- `false100_structural.jsonl`: 100 structurally ambiguous false variants.",
        "- `combined200_shuffled.jsonl`: true and false rows shuffled for mixed evaluation.",
        "- `manifest.jsonl`: source mapping and hidden expected correction metadata.",
        "",
        f"Shuffle seed: `{seed}`.",
        "",
        "Transform counts:",
        "",
    ]
    for key, value in counts.most_common():
        lines.append(f"- `{key}`: {value}")
    lines.extend(
        [
            "",
            "False variants intentionally avoid cheap final-answer flips. They prioritize:",
            "",
            "1. deleting modular/divisibility link hypotheses,",
            "2. deleting branch hypotheses for absolute-value/piecewise cases,",
            "3. deleting core equational hypotheses,",
            "4. weakening hypothesis equalities to inequalities.",
            "",
            "Each false row includes `false_transform` and `false_fix` so the hidden correction",
            "judge can require the model to say what must be restored to make the statement true.",
        ]
    )
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    raise SystemExit(main())
