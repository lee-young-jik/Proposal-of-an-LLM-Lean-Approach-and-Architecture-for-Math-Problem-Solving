#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any, Iterable


DECL_START_RE = re.compile(
    r"^\s*(?:@[^\n]*\s*)*(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Convert miniF2F-style data into the minimal evaluator JSONL schema: "
            "name, split, informal_prefix, formal_statement."
        )
    )
    parser.add_argument("input", type=Path, help="Input JSONL, Lean file, or directory.")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--split",
        help="Default split when the source row/file does not specify one.",
    )
    parser.add_argument(
        "--name-prefix",
        default="minif2f",
        help="Prefix used when an input row has no stable problem name.",
    )
    args = parser.parse_args()

    rows = list(load_input(args.input, default_split=args.split, name_prefix=args.name_prefix))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")

    print(f"Wrote {len(rows)} row(s) to {args.output}")
    return 0


def load_input(
    path: Path, *, default_split: str | None, name_prefix: str
) -> Iterable[dict[str, str]]:
    if path.is_dir():
        for child in sorted(path.rglob("*")):
            if child.suffix.lower() in {".jsonl", ".json", ".lean"}:
                yield from load_input(child, default_split=default_split, name_prefix=name_prefix)
        return

    suffix = path.suffix.lower()
    inferred_split = default_split or infer_split(path)
    if suffix == ".jsonl":
        yield from load_jsonl(path, default_split=inferred_split, name_prefix=name_prefix)
        return
    if suffix == ".json":
        yield from load_json(path, default_split=inferred_split, name_prefix=name_prefix)
        return
    if suffix == ".lean":
        yield from load_lean(path, default_split=inferred_split or "", name_prefix=name_prefix)
        return
    raise SystemExit(f"Unsupported input type: {path}")


def load_jsonl(
    path: Path, *, default_split: str | None, name_prefix: str
) -> Iterable[dict[str, str]]:
    with path.open(encoding="utf-8") as handle:
        for index, line in enumerate(handle):
            if not line.strip():
                continue
            yield normalize_row(
                json.loads(line),
                index=index,
                default_split=default_split,
                name_prefix=name_prefix,
            )


def load_json(
    path: Path, *, default_split: str | None, name_prefix: str
) -> Iterable[dict[str, str]]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(value, dict):
        if isinstance(value.get("data"), list):
            value = value["data"]
        elif isinstance(value.get("examples"), list):
            value = value["examples"]
        else:
            value = [value]
    if not isinstance(value, list):
        raise SystemExit(f"Unsupported JSON shape in {path}")
    for index, row in enumerate(value):
        yield normalize_row(
            row,
            index=index,
            default_split=default_split,
            name_prefix=name_prefix,
        )


def load_lean(
    path: Path, *, default_split: str, name_prefix: str
) -> Iterable[dict[str, str]]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    offsets = line_offsets(text)
    index = 0
    i = 0
    while i < len(lines):
        match = DECL_START_RE.match(lines[i])
        if not match:
            i += 1
            continue
        start = i
        block_lines = [lines[i]]
        while ":=" not in lines[i]:
            i += 1
            if i >= len(lines):
                break
            block_lines.append(lines[i])
        block = strip_proof("\n".join(block_lines).strip())
        name = match.group(2)
        informal = adjacent_doc_comment(lines, start) or f"Prove `{name}`."
        yield minimal_row(
            name=f"{name_prefix}_{name}",
            split=default_split,
            informal_prefix=informal,
            formal_statement=block,
        )
        index += 1
        i += 1


def line_offsets(text: str) -> list[int]:
    offsets: list[int] = []
    current = 0
    for line in text.splitlines(keepends=True):
        offsets.append(current)
        current += len(line)
    return offsets


def normalize_row(
    row: dict[str, Any],
    *,
    index: int,
    default_split: str | None,
    name_prefix: str,
) -> dict[str, str]:
    formal = first_text(
        row,
        "formal_statement",
        "formal",
        "lean_statement",
        "lean",
        "theorem",
    )
    if not formal:
        raise ValueError(f"Missing formal statement in row {index}")

    formal = strip_proof(formal)
    name = (
        first_text(row, "name", "problem_name", "problem_id", "id")
        or theorem_name(formal)
        or f"{name_prefix}_{index:04d}"
    )
    split = first_text(row, "split") or default_split or ""
    informal = first_text(
        row,
        "informal_prefix",
        "informal_statement",
        "natural_language",
        "nl_statement",
        "problem",
    )
    if not informal:
        statement = first_text(row, "statement")
        if statement and statement != formal:
            informal = statement
    if not informal:
        informal = f"Prove `{name}`."

    return minimal_row(
        name=name,
        split=split,
        informal_prefix=clean_doc_comment(informal),
        formal_statement=formal,
    )


def minimal_row(
    *,
    name: str,
    split: str,
    informal_prefix: str,
    formal_statement: str,
) -> dict[str, str]:
    return {
        "name": sanitize_name(name),
        "split": split,
        "informal_prefix": clean_doc_comment(informal_prefix),
        "formal_statement": formal_statement.strip(),
    }


def first_text(row: dict[str, Any], *keys: str) -> str:
    for key in keys:
        value = row.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ""


def clean_doc_comment(text: str) -> str:
    stripped = text.strip()
    if stripped.startswith("/--") and stripped.endswith("-/"):
        stripped = stripped[3:-2]
    return stripped.strip()


def adjacent_doc_comment(lines: list[str], decl_start: int) -> str:
    j = decl_start - 1
    while j >= 0 and not lines[j].strip():
        j -= 1
    if j < 0:
        return ""
    if "/--" in lines[j] and "-/" in lines[j]:
        return clean_doc_comment(lines[j])
    if "-/" not in lines[j]:
        return ""
    comment: list[str] = []
    while j >= 0:
        comment.append(lines[j])
        if "/--" in lines[j]:
            break
        j -= 1
    if j < 0 or "/--" not in comment[-1]:
        return ""
    return clean_doc_comment("\n".join(reversed(comment)))


def strip_proof(formal: str) -> str:
    text = remove_imports_and_comments(formal).strip()
    if ":=" in text:
        text = text.split(":=", 1)[0].rstrip() + " := by"
    text = re.sub(r"(?s):=\s*by\s*(?:sorry|admit)\s*$", ":= by", text)
    text = re.sub(r"(?s):=\s*(?:by\s*)?sorry\s*$", ":= by", text)
    text = re.sub(r"(?s):=\s*(?:by\s*)?admit\s*$", ":= by", text)
    if ":=" not in text:
        text = text.rstrip() + " := by"
    return text.strip()


def remove_imports_and_comments(text: str) -> str:
    lines = []
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("import ") or stripped.startswith("open ") or stripped.startswith("open scoped "):
            continue
        if stripped.startswith("/--") or stripped == "-/":
            continue
        lines.append(line)
    return "\n".join(lines)


def theorem_name(formal: str) -> str:
    match = re.search(r"\b(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)\b", formal)
    return match.group(1) if match else ""


def sanitize_name(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", name.strip()).strip("_")


def infer_split(path: Path) -> str:
    lowered = str(path).lower()
    for split in ("valid", "validation", "test", "train"):
        if split in lowered:
            return "valid" if split == "validation" else split
    return ""


if __name__ == "__main__":
    raise SystemExit(main())
