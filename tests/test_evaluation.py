from __future__ import annotations

from pathlib import Path
import json
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from single_orchestrator.evaluation import EvaluationConfig, ProofNetEvaluator
from single_orchestrator.dual_evaluation import DualEvaluationConfig, DualProofNetEvaluator
from single_orchestrator.model import ModelClientError
from single_orchestrator.prompts import BuiltPrompt
from single_orchestrator.proofnet import ProofNetExample


class RaisingModelClient:
    def complete(self, prompt: BuiltPrompt) -> str:
        raise ModelClientError(f"failed during {prompt.name}")


class EvaluationTest(unittest.TestCase):
    def test_single_evaluator_records_model_error_and_continues(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            output_dir = root / "out"
            output_path = output_dir / "results.jsonl"
            evaluator = ProofNetEvaluator(
                model_client=RaisingModelClient(),
                judge_model_client=RaisingModelClient(),
                config=EvaluationConfig(project_root=root, output_dir=output_dir),
            )
            examples = [
                ProofNetExample(
                    id="first",
                    informal_statement="Prove True.",
                    informal_proof="",
                    formal_statement="theorem first : True :=",
                    split="valid",
                ),
                ProofNetExample(
                    id="second",
                    informal_statement="Prove True.",
                    informal_proof="",
                    formal_statement="theorem second : True :=",
                    split="valid",
                ),
            ]

            results = evaluator.evaluate(examples, output_path)

            written = [
                json.loads(line)
                for line in output_path.read_text(encoding="utf-8").splitlines()
                if line.strip()
            ]
        self.assertEqual([result["id"] for result in results], ["first", "second"])
        self.assertEqual([result["final_status"] for result in results], ["not_solved", "not_solved"])
        self.assertEqual(len(written), 2)
        self.assertIn("failed during orchestrator.strategy", written[0]["rationale"])

    def test_single_evaluator_rejects_wrong_minif2f_project_root(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            evaluator = ProofNetEvaluator(
                model_client=RaisingModelClient(),
                config=EvaluationConfig(
                    project_root=root,
                    output_dir=root / "out",
                    verifier_prelude="import MiniF2F.ProblemImports",
                ),
            )

            with self.assertRaisesRegex(ValueError, "MiniF2F fixed prelude requires"):
                evaluator.evaluate([], root / "out" / "results.jsonl")

    def test_dual_evaluator_rejects_wrong_minif2f_project_root(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            evaluator = DualProofNetEvaluator(
                model_client=RaisingModelClient(),
                config=DualEvaluationConfig(
                    project_root=root,
                    output_dir=root / "out",
                    verifier_prelude="import MiniF2F.ProblemImports",
                ),
            )

            with self.assertRaisesRegex(ValueError, "MiniF2F fixed prelude requires"):
                evaluator.evaluate([], root / "out" / "results.jsonl")


if __name__ == "__main__":
    unittest.main()
