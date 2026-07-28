from __future__ import annotations

import json
import unittest

from single_orchestrator.false_review import FalseReviewRuntime


class FakeClient:
    def __init__(self, responses: dict[str, str]):
        self.responses = responses
        self.inputs: dict[str, dict] = {}

    def complete(self, prompt):
        self.inputs[prompt.name] = prompt.inputs
        return self.responses[prompt.name]


class FalseReviewRuntimeTest(unittest.TestCase):
    def test_reason_sees_only_clean_memory_and_check_sees_key(self) -> None:
        client = FakeClient(
            {
                "false_reason": json.dumps(
                    {"why": "The target uses 66 instead of 65.", "change": "66 to 65", "unclear": False}
                ),
                "false_check": json.dumps(
                    {"decision": "false", "why": "The inferred change exactly matches."}
                ),
            }
        )
        result = FalseReviewRuntime(client).review(
            memory=[
                {"trial_index": index, "informal": f"attempt {index}", "secret": "do not send"}
                for index in range(1, 4)
            ],
            answer_key={"transform": "65 to 66", "fix": ["66 to 65"], "label": "false"},
        )

        self.assertEqual(result["decision"], "false")
        self.assertEqual(set(client.inputs["false_reason"]), {"memory"})
        self.assertNotIn("secret", json.dumps(client.inputs["false_reason"]))
        self.assertNotIn("65 to 66", json.dumps(client.inputs["false_reason"]))
        self.assertEqual(set(client.inputs["false_check"]), {"claim", "key"})
        self.assertNotIn("label", client.inputs["false_check"]["key"])

    def test_unclear_reason_forces_next_round_without_check_call(self) -> None:
        client = FakeClient(
            {
                "false_reason": json.dumps(
                    {"why": "Maybe wrong.", "change": "", "unclear": True}
                )
            }
        )
        result = FalseReviewRuntime(client).review(
            memory=[{"trial": index, "reasoning": "failed"} for index in range(1, 4)],
            answer_key={"transform": "hidden", "fix": ["repair"]},
        )

        self.assertEqual(result["decision"], "next_round")
        self.assertNotIn("false_check", client.inputs)

    def test_dual_reason_receives_separate_truth_and_falsifier_memories(self) -> None:
        client = FakeClient(
            {
                "false_reason": json.dumps(
                    {
                        "why": "The conclusion claims 66 although the premises imply 65.",
                        "change": "replace 66 with 65",
                        "unclear": False,
                    }
                ),
                "false_check": json.dumps(
                    {
                        "decision": "false",
                        "why": "The diagnosis and repair exactly match the key.",
                    }
                ),
            }
        )
        result = FalseReviewRuntime(client).review_dual(
            truth_memory=[
                {
                    "trial_index": index,
                    "informal": f"truth attempt {index}",
                    "secret": "do not send",
                }
                for index in range(1, 4)
            ],
            falsifier_memory=[
                {
                    "informal": "The premises imply 65, not 66.",
                    "secret": "do not send",
                }
            ],
            answer_key={"transform": "65 to 66", "fix": ["replace 66 with 65"]},
        )

        self.assertEqual(result["decision"], "false")
        reason_inputs = client.inputs["false_reason"]
        self.assertEqual(
            set(reason_inputs), {"truth_memory", "falsifier_memory"}
        )
        self.assertEqual(len(reason_inputs["truth_memory"]), 3)
        self.assertEqual(len(reason_inputs["falsifier_memory"]), 1)
        self.assertNotIn("counter_reasoning", json.dumps(reason_inputs))
        self.assertNotIn("secret", json.dumps(reason_inputs))
        self.assertNotIn("65 to 66", json.dumps(reason_inputs))


if __name__ == "__main__":
    unittest.main()
