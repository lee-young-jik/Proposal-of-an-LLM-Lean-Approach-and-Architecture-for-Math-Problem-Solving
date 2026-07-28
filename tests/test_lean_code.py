from __future__ import annotations

import unittest

from single_orchestrator.lean_code import (
    complete_lean_source,
    lean_generation_rejection_reason,
)


class LeanCodeTest(unittest.TestCase):
    def test_bare_tactic_is_wrapped_with_formal_statement(self) -> None:
        source = complete_lean_source(
            "native_decide",
            "theorem target : 54 % 6 = 0 := by",
        )

        self.assertEqual(
            source,
            "theorem target : 54 % 6 = 0 := by\n  native_decide",
        )

    def test_simple_tactic_lines_are_indented_consistently(self) -> None:
        source = complete_lean_source(
            "rw [h]\n    norm_num",
            "theorem target : True := by",
        )

        self.assertEqual(
            source,
            "theorem target : True := by\n  rw [h]\n  norm_num",
        )

    def test_nested_have_body_keeps_relative_indentation(self) -> None:
        source = complete_lean_source(
            "have h : a + b = 27 := by\n  nlinarith [h₂]\n"
            "nlinarith [h₁, h]",
            "theorem target (a b : ℝ) (h₁ : a * b = 180) "
            "(h₂ : 2 * (a + b) = 54) : a ^ 2 + b ^ 2 = 369 := by",
        )

        self.assertIn("  have h : a + b = 27 := by\n    nlinarith [h₂]", source)
        self.assertIn("\n  nlinarith [h₁, h]", source)

    def test_body_indented_by_model_keeps_top_level_siblings(self) -> None:
        source = complete_lean_source(
            "have h : a + b = 27 := by\n"
            "    linarith\n"
            "  nlinarith [h₁, h]",
            "theorem target (a b : ℝ) (h₁ : a * b = 180) "
            "(h₂ : 2 * (a + b) = 54) : a ^ 2 + b ^ 2 = 369 := by",
        )

        self.assertIn("  have h : a + b = 27 := by\n    linarith", source)
        self.assertIn("\n  nlinarith [h₁, h]", source)
        self.assertNotIn("\n    nlinarith [h₁, h]", source)

    def test_tactic_let_line_drops_term_style_trailing_in(self) -> None:
        source = complete_lean_source(
            "let C : ℝ := 1 in\n"
            "have hC : C = 1 := by rfl\n"
            "exact hC",
            "theorem target : (1 : ℝ) = 1 := by",
        )

        self.assertIn("\n  let C : ℝ := 1\n", source)
        self.assertNotIn("let C : ℝ := 1 in", source)

    def test_sum_membership_notation_generated_with_in_is_normalized(self) -> None:
        source = complete_lean_source(
            "let A : ℝ := ∑ i in Finset.range k, Real.cos (a i)\n"
            "exact h",
            "theorem target (k : ℕ) (a : ℕ → ℝ) (h : True) : True := by",
        )

        self.assertIn("∑ i ∈ Finset.range k, Real.cos (a i)", source)
        self.assertNotIn("∑ i in Finset.range k", source)

    def test_model_imports_are_preserved_with_formal_statement(self) -> None:
        source = complete_lean_source(
            "import Mathlib.Data.Real.Basic\n\n"
            "theorem generated_target : True := by\n"
            "  trivial",
            "theorem target : True := by",
        )

        self.assertEqual(
            source,
            "import Mathlib.Data.Real.Basic\n\n"
            "theorem target : True := by\n"
            "  trivial",
        )

    def test_natural_language_non_proof_is_not_sent_to_lean(self) -> None:
        source = complete_lean_source(
            "No valid Lean proof exists: the statement is false as written.",
            "theorem target : False := by",
        )

        self.assertEqual(source, "")

    def test_natural_language_false_statement_variant_is_not_sent_to_lean(self) -> None:
        source = complete_lean_source(
            "No valid proof exists: the target statement is false for arbitrary `a`.",
            "theorem target : False := by",
        )

        self.assertEqual(source, "")

    def test_false_non_proof_reason_is_preserved_for_memory(self) -> None:
        reason = lean_generation_rejection_reason(
            "-- The provided statement is false for arbitrary `a`; "
            "for example, at `a = 1` the sum is `0`, not `25`."
        )

        self.assertIn("reported possible falsity", reason)
        self.assertIn("a = 1", reason)


if __name__ == "__main__":
    unittest.main()
