from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from single_orchestrator.proofnet import (
    attach_hidden_false_keys,
    filter_examples,
    load_proofnet_jsonl,
    safe_example_id,
)


class ProofNetLoaderTest(unittest.TestCase):
    def test_load_deepseek_jsonl_maps_informal_prefix_and_split(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            path = Path(raw_dir) / "proofnet.jsonl"
            rows = [
                {
                    "name": "exercise_valid",
                    "split": "valid",
                    "informal_prefix": "/-- Prove that True is true.-/\n",
                    "formal_statement": "theorem exercise_valid : True :=",
                    "goal": "⊢ True",
                    "header": "import Mathlib\n",
                },
                {
                    "name": "exercise_test",
                    "split": "test",
                    "informal_prefix": "/-- Prove that False is false.-/\n",
                    "formal_statement": "theorem exercise_test : False :=",
                    "goal": "⊢ False",
                    "header": "import Mathlib\n",
                },
            ]
            path.write_text(
                "".join(json.dumps(row) + "\n" for row in rows),
                encoding="utf-8",
            )

            examples = load_proofnet_jsonl(path, split="valid")

        self.assertEqual(len(examples), 1)
        self.assertEqual(examples[0].id, "exercise_valid")
        self.assertEqual(examples[0].informal_statement, "Prove that True is true.")
        self.assertEqual(examples[0].source_format, "deepseek-v1.5")
        self.assertEqual(examples[0].goal, "⊢ True")
        self.assertEqual(examples[0].header, "import Mathlib\n")
        self.assertEqual(examples[0].allowed_imports, ("Mathlib",))
        self.assertIn("Statement:", examples[0].problem_text)
        self.assertNotIn("Allowed imports", examples[0].problem_text)

    def test_filter_and_safe_id(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            path = Path(raw_dir) / "valid.jsonl"
            rows = [
                {
                    "name": f"exercise_{i}",
                    "split": "valid",
                    "informal_prefix": "/-- Prove True.-/",
                    "formal_statement": "theorem x : True :=",
                    "goal": "⊢ True",
                    "header": "import Mathlib\n",
                }
                for i in range(3)
            ]
            path.write_text(
                "".join(json.dumps(row) + "\n" for row in rows),
                encoding="utf-8",
            )
            examples = load_proofnet_jsonl(path)

        selected = filter_examples(examples, start=1, limit=1)
        self.assertEqual([example.id for example in selected], ["exercise_1"])
        self.assertEqual(safe_example_id("exercise 1/a"), "exercise_1_a")

    def test_load_minimal_jsonl_without_import_context(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            path = Path(raw_dir) / "minimal.jsonl"
            row = {
                "name": "minimal",
                "split": "valid",
                "informal_prefix": "Prove True.",
                "formal_statement": "theorem minimal : True :=",
            }
            path.write_text(json.dumps(row) + "\n", encoding="utf-8")

            examples = load_proofnet_jsonl(path, split="valid")

        self.assertEqual(len(examples), 1)
        self.assertEqual(examples[0].header, "")
        self.assertEqual(examples[0].goal, "")
        self.assertEqual(examples[0].allowed_imports, ())

    def test_normalizes_minif2f_answer_wrapper_in_formal_statement(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            path = Path(raw_dir) / "minif2f.jsonl"
            rows = [
                {
                    "name": "numeric_answer",
                    "split": "valid",
                    "informal_prefix": "Find the value.",
                    "formal_statement": "theorem numeric_answer : x = answer(7) := by",
                },
                {
                    "name": "tuple_answer",
                    "split": "valid",
                    "informal_prefix": "Find the point.",
                    "formal_statement": "theorem tuple_answer : p = answer((15, -11)) := by",
                },
            ]
            path.write_text(
                "".join(json.dumps(row) + "\n" for row in rows),
                encoding="utf-8",
            )

            examples = load_proofnet_jsonl(path, split="valid")

        self.assertEqual(examples[0].formal_statement, "theorem numeric_answer : x = (7) := by")
        self.assertEqual(
            examples[1].formal_statement,
            "theorem tuple_answer : p = ((15, -11)) := by",
        )

    def test_load_custom_split_name(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            path = Path(raw_dir) / "false.jsonl"
            rows = [
                {
                    "name": "false_example",
                    "split": "false_diverse_100",
                    "informal_prefix": "/-- Prove the modified target.-/",
                    "formal_statement": "theorem false_example : False :=",
                    "goal": "⊢ False",
                    "header": "import Mathlib\n",
                },
                {
                    "name": "valid_example",
                    "split": "valid",
                    "informal_prefix": "/-- Prove True.-/",
                    "formal_statement": "theorem valid_example : True :=",
                    "goal": "⊢ True",
                    "header": "import Mathlib\n",
                },
            ]
            path.write_text(
                "".join(json.dumps(row) + "\n" for row in rows),
                encoding="utf-8",
            )

            examples = load_proofnet_jsonl(path, split="false_diverse_100")

        self.assertEqual([example.id for example in examples], ["false_example"])

    def test_attaches_private_false_keys_without_public_row_leakage(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            public_path = Path(raw_dir) / "mixed.jsonl"
            labels_path = Path(raw_dir) / "labels.jsonl"
            public_rows = [
                {
                    "name": "problem_01",
                    "split": "blind",
                    "informal_prefix": "A deliberately false problem.",
                    "formal_statement": "theorem problem_01 : False := by",
                },
                {
                    "name": "problem_02",
                    "split": "blind",
                    "informal_prefix": "A true problem.",
                    "formal_statement": "theorem problem_02 : True := by",
                },
            ]
            label_rows = [
                {
                    "name": "problem_01",
                    "gold": "false",
                    "false_transform": "removed hypothesis h",
                    "expected_false_fix": ["add hypothesis h"],
                },
                {"name": "problem_02", "gold": "true"},
            ]
            public_path.write_text(
                "".join(json.dumps(row) + "\n" for row in public_rows),
                encoding="utf-8",
            )
            labels_path.write_text(
                "".join(json.dumps(row) + "\n" for row in label_rows),
                encoding="utf-8",
            )

            public_examples = load_proofnet_jsonl(public_path, split="blind")
            examples = attach_hidden_false_keys(public_examples, labels_path)

        self.assertEqual(public_examples[0].false_fix, ())
        self.assertEqual(public_examples[0].false_transform, "")
        self.assertEqual(examples[0].false_transform, "removed hypothesis h")
        self.assertEqual(examples[0].false_fix, ("add hypothesis h",))
        self.assertEqual(examples[1].false_fix, ())


if __name__ == "__main__":
    unittest.main()
