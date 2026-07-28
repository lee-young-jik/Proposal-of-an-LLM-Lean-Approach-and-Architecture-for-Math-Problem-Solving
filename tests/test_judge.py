from __future__ import annotations

from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from single_orchestrator.judge import LLMJudge, _parse_json_response
from single_orchestrator.prompts import BuiltPrompt
from single_orchestrator.proofnet import ProofNetExample


class FakeJudgeModel:
    def __init__(self, response: str):
        self.response = response
        self.calls: list[BuiltPrompt] = []

    def complete(self, prompt: BuiltPrompt) -> str:
        self.calls.append(prompt)
        return self.response


class JudgeTest(unittest.TestCase):
    def test_parse_json_response_from_fence(self) -> None:
        payload = _parse_json_response(
            '```json\n{"equivalent": true, "score": 1.0, "rationale": "same"}\n```'
        )

        self.assertTrue(payload["equivalent"])
        self.assertEqual(payload["score"], 1.0)

    def test_judge_returns_structured_result(self) -> None:
        model = FakeJudgeModel(
            '{"equivalent": true, "score": 1.0, "rationale": "candidate matches"}'
        )
        judge = LLMJudge(model)
        example = ProofNetExample(
            id="unused_example_id",
            informal_statement="Prove True.",
            informal_proof="trivial",
            formal_statement="theorem exercise_1 : True :=",
        )

        result = judge.judge(example, "theorem generated : True := by trivial")

        self.assertTrue(result.equivalent)
        self.assertEqual(result.score, 1.0)
        self.assertEqual(model.calls[0].name, "llm_judge.proofnet_equivalence")
        self.assertEqual(set(model.calls[0].inputs), {"gold_formal", "candidate_lean"})
        self.assertNotIn("unused_example_id", model.calls[0].text)
        self.assertNotIn("Informal proof", model.calls[0].text)
        self.assertNotIn("Informal statement", model.calls[0].text)

    def test_judge_context_only_sends_gold_and_candidate(self) -> None:
        model = FakeJudgeModel(
            '{"equivalent": true, "score": 1.0, "rationale": "candidate matches"}'
        )
        judge = LLMJudge(model)

        result = judge.judge_context(
            {"formal_statement": "theorem exercise_1 : True :="},
            "theorem generated : True := by trivial",
        )

        self.assertTrue(result.equivalent)
        call = model.calls[0]
        self.assertEqual(set(call.inputs), {"gold_formal", "candidate_lean"})
        self.assertNotIn("truth_memory", call.inputs)
        self.assertNotIn("falsity_memory", call.inputs)
        self.assertNotIn("trial_memory", call.inputs)
        self.assertNotIn("falsity", call.text.lower())
        self.assertNotIn("false opinion", call.text.lower())


if __name__ == "__main__":
    unittest.main()
