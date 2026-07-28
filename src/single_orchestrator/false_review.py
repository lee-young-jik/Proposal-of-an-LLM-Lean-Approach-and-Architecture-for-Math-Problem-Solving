from __future__ import annotations

import json
import os
from contextlib import nullcontext
from typing import Any

from .model import ModelClient, ModelClientError
from .prompts import BuiltPrompt
from .trace import traceable


REASON_PROMPT = """System:
You diagnose why a Lean statement is not correct from one round of three trial
memories. You do not know how the dataset author changed the problem, and you
must not guess from a mutation catalogue or hidden answer. Use only the memory.
State the concrete mathematical failure and the exact change you infer. If the
memory does not determine both clearly, set unclear to true. Return JSON only.

User:
Three-trial memory:
{memory}

Return exactly these keys:
{{"why": "concrete reason the statement is wrong", "change": "exact inferred change or repair", "unclear": true_or_false}}
"""

DUAL_REASON_PROMPT = """System:
You diagnose why a Lean statement is not correct using two separate memory
sections. The truth memory contains three attempts to prove the statement. The
falsifier memory contains the direct mathematical criticism produced by the
Falsifier Agent. Read and compare both sections, but do not merge their roles.
You do not know how the dataset author changed the problem, and you must not
guess from a mutation catalogue or hidden answer. A Lean syntax, tactic,
library, or timeout failure alone is not a mathematical reason that the
statement is false. State the concrete mathematical failure and the exact
change needed in the statement. If the memories do not determine both clearly,
set unclear to true. Return JSON only.

User:
Truth memory:
{truth_memory}

Falsifier memory:
{falsifier_memory}

Return exactly these keys:
{{"why": "concrete reason the statement is wrong", "change": "exact inferred change or repair", "unclear": true_or_false}}
"""


CHECK_PROMPT = """System:
You are the final conservative checker. Compare the diagnosis with the private
dataset key. Do not invent a new diagnosis. Return false only when the diagnosis
clearly identifies why the statement is false and its inferred change matches
the recorded transform and repair in mathematical meaning. Vague, partial,
different, or uncertain matches must return next_round. Return JSON only.

User:
Diagnosis:
{claim}

Private dataset key:
{key}

Return exactly these keys:
{{"decision": "false" or "next_round", "why": "short comparison reason"}}
"""


def _reason_trace_input(values: dict[str, Any]) -> dict[str, Any]:
    return {"memory": values.get("memory", [])}


def _dual_reason_trace_input(values: dict[str, Any]) -> dict[str, Any]:
    return {
        "truth_memory": values.get("truth_memory", []),
        "falsifier_memory": values.get("falsifier_memory", []),
    }


def _reason_trace_output(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        return {"why": "", "change": "", "unclear": True}
    return {
        "why": value.get("why", ""),
        "change": value.get("change", ""),
        "unclear": value.get("unclear", True),
    }


def _check_trace_input(values: dict[str, Any]) -> dict[str, Any]:
    return {"claim": values.get("claim", {}), "key": values.get("key", {})}


def _check_trace_output(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        return {"decision": "next_round", "why": "Invalid output."}
    return {
        "decision": value.get("decision", "next_round"),
        "why": value.get("why", ""),
    }


class FalseReviewRuntime:
    """Minimal two-model False review used by the isolated test environment."""

    def __init__(self, model_client: ModelClient):
        self.model_client = model_client

    def review(
        self,
        *,
        memory: list[dict[str, Any]],
        answer_key: dict[str, Any],
    ) -> dict[str, Any]:
        if len(memory) != 3:
            return {
                "decision": "next_round",
                "why": "Exactly three trial memories are required.",
                "claim": {"why": "", "change": "", "unclear": True},
            }
        with self._trace_context():
            claim = self.reason(memory=self._clean_memory(memory))
        with self._trace_context():
            decision = self.check(claim=claim, key=self._clean_key(answer_key))
        return {**decision, "claim": claim}

    def review_dual(
        self,
        *,
        truth_memory: list[dict[str, Any]],
        falsifier_memory: list[dict[str, Any]],
        answer_key: dict[str, Any],
    ) -> dict[str, Any]:
        if len(truth_memory) != 3:
            return {
                "decision": "next_round",
                "why": "Exactly three truth trial memories are required.",
                "claim": {"why": "", "change": "", "unclear": True},
            }
        if not falsifier_memory:
            return {
                "decision": "next_round",
                "why": "At least one Falsifier memory is required.",
                "claim": {"why": "", "change": "", "unclear": True},
            }
        with self._trace_context():
            claim = self.reason_dual(
                truth_memory=self._clean_memory(truth_memory),
                falsifier_memory=self._clean_memory(falsifier_memory),
            )
        with self._trace_context():
            decision = self.check(claim=claim, key=self._clean_key(answer_key))
        return {**decision, "claim": claim}

    @traceable(
        name="false_reason",
        run_type="llm",
        process_inputs=_reason_trace_input,
        process_outputs=_reason_trace_output,
    )
    def reason(self, *, memory: list[dict[str, Any]]) -> dict[str, Any]:
        prompt = BuiltPrompt(
            name="false_reason",
            version="v1",
            inputs={"memory": memory},
            text=REASON_PROMPT.format(
                memory=json.dumps(memory, ensure_ascii=False, indent=2)
            ),
        )
        try:
            raw = self.model_client.complete(prompt)
            parsed = self._parse_json(raw)
        except (ModelClientError, ValueError, TypeError, json.JSONDecodeError) as exc:
            return {"why": f"Reason model failed: {exc}", "change": "", "unclear": True}

        why = str(parsed.get("why", "")).strip()
        change = str(parsed.get("change", "")).strip()
        unclear = parsed.get("unclear") is not False
        if not why or not change:
            unclear = True
        return {"why": why, "change": change, "unclear": unclear}

    @traceable(
        name="false_reason",
        run_type="llm",
        process_inputs=_dual_reason_trace_input,
        process_outputs=_reason_trace_output,
    )
    def reason_dual(
        self,
        *,
        truth_memory: list[dict[str, Any]],
        falsifier_memory: list[dict[str, Any]],
    ) -> dict[str, Any]:
        prompt = BuiltPrompt(
            name="false_reason",
            version="v2-dual-memory",
            inputs={
                "truth_memory": truth_memory,
                "falsifier_memory": falsifier_memory,
            },
            text=DUAL_REASON_PROMPT.format(
                truth_memory=json.dumps(
                    truth_memory, ensure_ascii=False, indent=2
                ),
                falsifier_memory=json.dumps(
                    falsifier_memory, ensure_ascii=False, indent=2
                ),
            ),
        )
        try:
            raw = self.model_client.complete(prompt)
            parsed = self._parse_json(raw)
        except (ModelClientError, ValueError, TypeError, json.JSONDecodeError) as exc:
            return {"why": f"Reason model failed: {exc}", "change": "", "unclear": True}

        why = str(parsed.get("why", "")).strip()
        change = str(parsed.get("change", "")).strip()
        unclear = parsed.get("unclear") is not False
        if not why or not change:
            unclear = True
        return {"why": why, "change": change, "unclear": unclear}

    @traceable(
        name="false_check",
        run_type="llm",
        process_inputs=_check_trace_input,
        process_outputs=_check_trace_output,
    )
    def check(
        self,
        *,
        claim: dict[str, Any],
        key: dict[str, Any],
    ) -> dict[str, str]:
        if (
            claim.get("unclear") is not False
            or not str(claim.get("why", "")).strip()
            or not str(claim.get("change", "")).strip()
            or not key.get("transform")
            or not key.get("fix")
        ):
            return {
                "decision": "next_round",
                "why": "Diagnosis or private key is incomplete or uncertain.",
            }

        prompt = BuiltPrompt(
            name="false_check",
            version="v1",
            inputs={"claim": claim, "key": key},
            text=CHECK_PROMPT.format(
                claim=json.dumps(claim, ensure_ascii=False, indent=2),
                key=json.dumps(key, ensure_ascii=False, indent=2),
            ),
        )
        try:
            raw = self.model_client.complete(prompt)
            parsed = self._parse_json(raw)
        except (ModelClientError, ValueError, TypeError, json.JSONDecodeError) as exc:
            return {"decision": "next_round", "why": f"Check model failed: {exc}"}

        decision = str(parsed.get("decision", "next_round")).strip()
        why = str(parsed.get("why", "")).strip()
        if decision != "false" or not why:
            return {"decision": "next_round", "why": why or "Match was not proven."}
        return {"decision": "false", "why": why}

    @staticmethod
    def _clean_key(answer_key: dict[str, Any]) -> dict[str, Any]:
        transform = str(answer_key.get("transform", "")).strip()
        raw_fix = answer_key.get("fix", [])
        fixes = (
            [str(item).strip() for item in raw_fix if str(item).strip()]
            if isinstance(raw_fix, list)
            else [str(raw_fix).strip()]
            if str(raw_fix).strip()
            else []
        )
        return {"transform": transform, "fix": fixes}

    @staticmethod
    def _clean_memory(memory: list[dict[str, Any]]) -> list[dict[str, Any]]:
        cleaned: list[dict[str, Any]] = []
        for index, record in enumerate(memory, start=1):
            reasoning = (
                record.get("reasoning")
                or record.get("informal")
                or record.get("attempt")
                or ""
            )
            values = {
                "trial": record.get("trial") or record.get("trial_index") or index,
                "lane": str(record.get("lane", "")).strip(),
                "reasoning": str(reasoning).strip(),
                "counter_reasoning": str(record.get("counter_reasoning", "")).strip(),
                "lean_error": str(
                    record.get("lean_error") or record.get("lean_error_log") or ""
                ).strip(),
                "retry": str(record.get("retry") or record.get("retry_plan") or "").strip(),
            }
            cleaned.append(
                {key: value for key, value in values.items() if value not in ("", None)}
            )
        return cleaned

    @staticmethod
    def _parse_json(raw: str) -> dict[str, Any]:
        text = raw.strip()
        if text.startswith("```"):
            lines = text.splitlines()[1:]
            if lines and lines[-1].strip() == "```":
                lines.pop()
            text = "\n".join(lines).strip()
        parsed = json.loads(text)
        if not isinstance(parsed, dict):
            raise TypeError("model output must be a JSON object")
        return parsed

    @staticmethod
    def _trace_context():
        project = os.getenv("DUAL_ARC_FALSE_REVIEW_PROJECT", "").strip()
        if not project:
            return nullcontext()
        try:
            from langsmith import tracing_context
        except ImportError:
            return nullcontext()
        return tracing_context(enabled=True, project_name=project)
