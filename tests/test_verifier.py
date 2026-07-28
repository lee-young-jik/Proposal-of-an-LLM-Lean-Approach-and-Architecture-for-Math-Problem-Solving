from __future__ import annotations

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from single_orchestrator.verifier import LakeVerifier, _default_runner


class LakeVerifierTest(unittest.TestCase):
    def test_default_runner_enforces_wall_clock_timeout(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            with self.assertRaises(subprocess.TimeoutExpired):
                _default_runner(
                    [sys.executable, "-c", "import time; time.sleep(5)"],
                    root,
                    1,
                )

    def test_default_runner_enforces_process_group_memory_limit(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            with patch("single_orchestrator.verifier.MAX_VERIFIER_RSS_KIB", 1):
                result = _default_runner(
                    [sys.executable, "-c", "import time; time.sleep(5)"],
                    root,
                    0,
                )

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("configured process-group memory limit", result.stderr)

    def test_success_failure_and_timeout_have_same_schema(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)

            success = LakeVerifier(root, command_runner=self._success).verify("theorem x : 1 = 1 := by rfl")
            failure = LakeVerifier(root, command_runner=self._failure).verify("theorem x : 1 = 2 := by rfl")
            timeout = LakeVerifier(root, command_runner=self._timeout).verify("theorem x : 1 = 1 := by rfl")

        self.assertEqual(set(success), set(failure))
        self.assertEqual(set(success), set(timeout))
        self.assertTrue(success["success"])
        self.assertFalse(failure["success"])
        self.assertFalse(timeout["success"])
        self.assertTrue(timeout["timed_out"])

    def test_prelude_is_added_when_code_has_no_import(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            verifier = LakeVerifier(
                root,
                prelude="import Mathlib.Data.Nat.Basic\n",
                command_runner=self._success,
            )

            result = verifier.verify("theorem x : True := by trivial")

        self.assertTrue(result["formal_state"].startswith("import Mathlib.Data.Nat.Basic"))

    def test_prelude_is_added_before_existing_import(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            verifier = LakeVerifier(
                root,
                prelude="import MiniF2F.ProblemImports\nopen scoped Real\n",
                command_runner=self._success,
            )

            result = verifier.verify(
                "import Mathlib.Data.Real.Basic\n\ntheorem x : True := by trivial"
            )

        self.assertIn("import MiniF2F.ProblemImports", result["formal_state"])
        self.assertIn("import Mathlib.Data.Real.Basic", result["formal_state"])
        self.assertLess(
            result["formal_state"].index("import MiniF2F.ProblemImports"),
            result["formal_state"].index("import Mathlib.Data.Real.Basic"),
        )

    def test_sorry_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x : False := by sorry"
            )

        self.assertFalse(result["success"])
        self.assertTrue(result["has_prohibited_placeholder"])
        self.assertIn("prohibited placeholder", result["lean_error_log"])

    def test_field_simp_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x : 1 = 1 := by\n  field_simp"
            )

        self.assertFalse(result["success"])
        self.assertTrue(result["has_prohibited_placeholder"])
        self.assertIn("prohibited heavy tactic", result["lean_error_log"])
        self.assertIn("field_simp", result["lean_error_log"])

    def test_nlinarith_is_allowed_but_timeout_is_annotated(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._timeout).verify(
                "theorem x : 1 = 1 := by\n  nlinarith"
            )

        self.assertFalse(result["success"])
        self.assertTrue(result["timed_out"])
        self.assertFalse(result["has_prohibited_placeholder"])
        self.assertIn("lake build timed out", result["lean_error_log"])
        self.assertIn("used `nlinarith`", result["lean_error_log"])

    def test_linarith_timeout_is_annotated(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._timeout).verify(
                "theorem x : 1 = 1 := by\n  linarith"
            )

        self.assertFalse(result["success"])
        self.assertTrue(result["timed_out"])
        self.assertFalse(result["has_prohibited_placeholder"])
        self.assertIn("lake build timed out", result["lean_error_log"])
        self.assertIn("used `linarith`", result["lean_error_log"])

    def test_strict_timeout_guard_rejects_linarith_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(
                root,
                strict_timeout_guard=True,
                command_runner=self._unexpected,
            ).verify("theorem x : 1 = 1 := by\n  linarith")

        self.assertFalse(result["success"])
        self.assertFalse(result["timed_out"])
        self.assertIn("Strict timeout guard", result["lean_error_log"])
        self.assertIn("linarith", result["lean_error_log"])

    def test_strict_timeout_guard_rejects_broad_norm_num_at_target(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(
                root,
                strict_timeout_guard=True,
                command_runner=self._unexpected,
            ).verify(
                "theorem x (n : ℕ) (h : n ≤ 10) : n = 3 := by\n"
                "  interval_cases n <;> norm_num at h ⊢"
            )

        self.assertFalse(result["success"])
        self.assertFalse(result["timed_out"])
        self.assertIn("Strict timeout guard", result["lean_error_log"])
        self.assertIn("norm_num at ... ⊢", result["lean_error_log"])

    def test_strict_timeout_guard_rejects_real_rw_norm_num_cleanup(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(
                root,
                strict_timeout_guard=True,
                command_runner=self._unexpected,
            ).verify(
                "theorem x (a b : ℝ) (h : a = b) : a = b := by\n"
                "  rw [h]\n"
                "  norm_num"
            )

        self.assertFalse(result["success"])
        self.assertFalse(result["timed_out"])
        self.assertIn("Strict timeout guard", result["lean_error_log"])
        self.assertIn("Real-valued theorem", result["lean_error_log"])

    def test_strict_timeout_guard_rejects_decide_with_binders(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(
                root,
                strict_timeout_guard=True,
                command_runner=self._unexpected,
            ).verify("theorem x (n : ℕ) : n = n := by\n  native_decide")

        self.assertFalse(result["success"])
        self.assertFalse(result["timed_out"])
        self.assertIn("Strict timeout guard", result["lean_error_log"])
        self.assertIn("theorem with binders", result["lean_error_log"])

    def test_real_log_broad_arithmetic_automation_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "import MiniF2F.ProblemImports\n\n"
                "theorem x (a b c : ℝ) : True := by\n"
                "  have h : Real.log a = Real.log b := by\n"
                "    nlinarith\n"
                "  have h2 : Real.log b = Real.log c := by\n"
                "    linarith\n"
                "  trivial"
            )

        self.assertFalse(result["success"])
        self.assertFalse(result["has_prohibited_placeholder"])
        self.assertIn("broad arithmetic automation", result["lean_error_log"])
        self.assertIn("Real.log", result["lean_error_log"])

    def test_real_log_single_linarith_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "import MiniF2F.ProblemImports\n\n"
                "theorem x (a b : ℝ) : True := by\n"
                "  have h : Real.log a = Real.log b := by\n"
                "    linarith\n"
                "  trivial"
            )

        self.assertFalse(result["success"])
        self.assertFalse(result["has_prohibited_placeholder"])
        self.assertIn("broad arithmetic automation", result["lean_error_log"])
        self.assertIn("linarith", result["lean_error_log"])

    def test_real_log_coercion_order_pattern_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "import MiniF2F.ProblemImports\n\n"
                "theorem x (a b : ℕ) : True := by\n"
                "  have hlog : Real.log (a : ℝ) = Real.log a := by rfl\n"
                "  have h : (1 : ℝ) < a * b := by\n"
                "    have h' := mul_lt_mul_of_pos_left\n"
                "    trivial\n"
                "  trivial"
            )

        self.assertFalse(result["success"])
        self.assertFalse(result["has_prohibited_placeholder"])
        self.assertIn("mul_lt_mul_of_pos_left", result["lean_error_log"])
        self.assertIn("Nat/Real type mismatches", result["lean_error_log"])

    def test_real_log_fragile_division_rewrite_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "import MiniF2F.ProblemImports\n\n"
                "theorem x (a b : ℝ) : True := by\n"
                "  have hlog : Real.log a ≠ 0 := by exact one_ne_zero\n"
                "  rw [div_mul_eq_mul_div, mul_div_cancel₀ _ hlog]\n"
                "  trivial"
            )

        self.assertFalse(result["success"])
        self.assertFalse(result["has_prohibited_placeholder"])
        self.assertIn("fragile division rewrites", result["lean_error_log"])
        self.assertIn("div_eq_iff", result["lean_error_log"])

    def test_unavailable_cbrt_api_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x : True := by\n  have h : True := by trivial\n  exact h\n"
                "  have y := Real.cbrt 2"
            )

        self.assertFalse(result["success"])
        self.assertTrue(result["has_prohibited_placeholder"])
        self.assertIn("unavailable API", result["lean_error_log"])
        self.assertIn("Real.cbrt", result["lean_error_log"])

    def test_known_unavailable_minif2f_api_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x : True := by\n"
                "  have h := Polynomial.irreducible_X_pow_sub_C\n"
                "  trivial"
            )

        self.assertFalse(result["success"])
        self.assertTrue(result["has_prohibited_placeholder"])
        self.assertIn("unavailable API", result["lean_error_log"])
        self.assertIn("Polynomial.irreducible_X_pow_sub_C", result["lean_error_log"])

    def test_known_unavailable_nat_pos_of_gt_api_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x : True := by\n"
                "  have h := Nat.pos_of_gt\n"
                "  trivial"
            )

        self.assertFalse(result["success"])
        self.assertTrue(result["has_prohibited_placeholder"])
        self.assertIn("unavailable API", result["lean_error_log"])
        self.assertIn("Nat.pos_of_gt", result["lean_error_log"])

    def test_broad_imports_are_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "import Mathlib\n\ntheorem x : True := by trivial"
        )

        self.assertFalse(result["success"])
        self.assertFalse(result["has_prohibited_placeholder"])
        self.assertIn("broad module `Mathlib`", result["lean_error_log"])

    def test_problem_imports_are_allowed_as_common_minif2f_prelude(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._success).verify(
                "import MiniF2F.ProblemImports\n\ntheorem x : True := by trivial"
        )

        self.assertTrue(result["success"])

    def test_problem_imports_adds_heartbeat_limit(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._success).verify(
                "import MiniF2F.ProblemImports\n\ntheorem x : True := by trivial"
            )

        self.assertTrue(result["success"])
        self.assertIn("set_option maxHeartbeats 0", result["formal_state"])
        self.assertLess(
            result["formal_state"].index("import MiniF2F.ProblemImports"),
            result["formal_state"].index("set_option maxHeartbeats"),
        )
        self.assertLess(
            result["formal_state"].index("set_option maxHeartbeats"),
            result["formal_state"].index("theorem x"),
        )

    def test_problem_imports_replaces_generated_heartbeat_limit(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._success).verify(
                "import MiniF2F.ProblemImports\n\n"
                "set_option maxHeartbeats 200000\n\n"
                "theorem x : True := by trivial"
            )

        self.assertTrue(result["success"])
        self.assertEqual(
            result["formal_state"].count("set_option maxHeartbeats 0"), 1
        )

    def test_interval_cases_norm_num_target_is_rewritten_to_avoid_no_goals_failure(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._success).verify(
                "theorem x (n : ℕ) (h : n ≤ 9) : n = n := by\n"
                "  interval_cases n <;> norm_num at h ⊢"
            )

        self.assertTrue(result["success"])
        self.assertIn("interval_cases n <;> simp_all", result["formal_state"])
        self.assertNotIn("norm_num at h ⊢", result["formal_state"])

    def test_large_explicit_finset_norm_num_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x : "
                "({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset ℕ).card = 9 := by\n"
                "  norm_num"
            )

        self.assertFalse(result["success"])
        self.assertIsNone(result["returncode"])
        self.assertIn("large Finset", result["lean_error_log"])

    def test_finset_interval_bare_simp_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x : (Finset.Icc (-12 : ℤ) 4).card = 17 := by\n"
                "  simp"
            )

        self.assertFalse(result["success"])
        self.assertIsNone(result["returncode"])
        self.assertIn("large Finset", result["lean_error_log"])

    def test_finset_interval_norm_num_with_lemma_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x : (Finset.Icc (-12 : ℤ) 4).card = 17 := by\n"
                "  norm_num [Finset.card_Icc]"
            )

        self.assertFalse(result["success"])
        self.assertIsNone(result["returncode"])
        self.assertIn("large Finset", result["lean_error_log"])

    def test_interval_cases_simp_all_target_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x (a : ℕ) (h : a < 24) : a = a := by\n"
                "  interval_cases a <;> simp_all at h ⊢"
            )

        self.assertFalse(result["success"])
        self.assertIsNone(result["returncode"])
        self.assertIn("every branch", result["lean_error_log"])

    def test_interval_cases_simp_all_with_small_bound_is_still_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x (a : ℕ) (h : a ≤ 4) : a = a := by\n"
                "  interval_cases a <;> simp_all at h ⊢"
            )

        self.assertFalse(result["success"])
        self.assertIsNone(result["returncode"])

    def test_interval_cases_bare_simp_all_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x (a : ℕ) (h : a ≤ 24) : a = a := by\n"
                "  interval_cases a <;> simp_all"
            )

        self.assertFalse(result["success"])
        self.assertIsNone(result["returncode"])
        self.assertIn("every branch", result["lean_error_log"])

    def test_interval_cases_simp_all_at_hypothesis_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x (a : ℕ) (h : a ≤ 24) : a = a := by\n"
                "  interval_cases a <;> simp_all at h"
            )

        self.assertFalse(result["success"])
        self.assertIsNone(result["returncode"])
        self.assertIn("every branch", result["lean_error_log"])

    def test_chained_interval_cases_simp_all_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x (a b : ℕ) (h : a + b = 3) : a = a := by\n"
                "  interval_cases a <;> interval_cases b <;> simp_all at h ⊢"
            )

        self.assertFalse(result["success"])
        self.assertIsNone(result["returncode"])
        self.assertIn("every branch", result["lean_error_log"])

    def test_omega_disjunction_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x (a : ℕ) (h : a * a = 4) : a = 2 := by\n"
                "  have hcases : a = 2 ∨ a = 0 := by\n"
                "    omega\n"
                "  omega"
            )

        self.assertFalse(result["success"])
        self.assertIsNone(result["returncode"])
        self.assertIn("disjunction", result["lean_error_log"])

    def test_bare_omega_on_nonlinear_theorem_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x (a b : ℕ) (h : a * b = 4) : a + b > 0 := by\n"
                "  omega"
            )

        self.assertFalse(result["success"])
        self.assertIsNone(result["returncode"])
        self.assertIn("nonlinear theorem", result["lean_error_log"])

    def test_interval_cases_all_goals_simp_all_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x (a : ℕ) (h : a ≤ 24) : a = a := by\n"
                "  interval_cases a\n"
                "  all_goals\n"
                "    simp_all [pow_two]"
            )

        self.assertFalse(result["success"])
        self.assertIsNone(result["returncode"])
        self.assertIn("every branch", result["lean_error_log"])

    def test_large_interval_cases_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x (a : ℕ) (h : a < 24) : a = a := by\n"
                "  interval_cases a\n"
                "  all_goals rfl"
            )

        self.assertFalse(result["success"])
        self.assertIsNone(result["returncode"])
        self.assertIn("24 branches", result["lean_error_log"])

    def test_broad_tactic_import_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "import Mathlib.Tactic\n\ntheorem x : True := by trivial"
        )

        self.assertFalse(result["success"])
        self.assertFalse(result["has_prohibited_placeholder"])
        self.assertIn("Mathlib.Tactic", result["lean_error_log"])

    def test_known_bad_import_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            (root / ".lake" / "packages" / "mathlib" / "Mathlib" / "Tactic").mkdir(
                parents=True
            )
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "import Mathlib.Tactic.Nlinarith\n\ntheorem x : True := by trivial"
        )

        self.assertFalse(result["success"])
        self.assertFalse(result["has_prohibited_placeholder"])
        self.assertIn("unavailable module", result["lean_error_log"])
        self.assertIn("Mathlib.Tactic.Nlinarith", result["lean_error_log"])

    def test_malformed_indentation_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "theorem x : True := by\n"
                "  have h : True := trivial\n"
                "    have h2 : True := trivial\n"
                "  exact h"
            )

        self.assertFalse(result["success"])
        self.assertTrue(result["has_prohibited_placeholder"])
        self.assertIn("malformed", result["lean_error_log"])
        self.assertIn("indentation", result["lean_error_log"])

    def test_target_mismatch_is_rejected_before_lake_build(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            target = "theorem target (x y : ℚ) : x.den = y.den := by"
            result = LakeVerifier(root, command_runner=self._unexpected).verify(
                "example : ¬ (∀ x y : ℚ, x.den = y.den) := by\n"
                "  intro h\n"
                "  have := h 0 (1 / 2)\n"
                "  norm_num at this",
                formal_statement=target,
            )

        self.assertFalse(result["success"])
        self.assertIsNone(result["returncode"])
        self.assertIn("expected exactly one top-level theorem", result["lean_error_log"])

    def test_existing_import_is_preserved(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            verifier = LakeVerifier(
                root,
                prelude="import Mathlib.Data.Nat.Basic\n",
                command_runner=self._success,
            )

            result = verifier.verify(
                "import Mathlib.Topology.MetricSpace.Basic\n\ntheorem x : True := by trivial"
            )

        self.assertIn("import Mathlib.Topology.MetricSpace.Basic", result["formal_state"])
        self.assertIn("import Mathlib.Data.Nat.Basic", result["formal_state"])

    def test_known_bad_import_is_rewritten_when_candidate_exists(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            (root / ".lake" / "packages" / "mathlib" / "Mathlib" / "Tactic").mkdir(
                parents=True
            )
            (root / ".lake" / "packages" / "mathlib" / "Mathlib" / "Tactic" / "Linarith.lean").write_text(
                "", encoding="utf-8"
            )
            result = LakeVerifier(root, command_runner=self._success).verify(
                "import Mathlib.Tactic.Nlinarith\n\ntheorem x : True := by trivial"
            )

        self.assertTrue(result["success"])
        self.assertIn("import Mathlib.Tactic.Linarith", result["formal_state"])
        self.assertNotIn("import Mathlib.Tactic.Nlinarith", result["formal_state"])

    @staticmethod
    def _success(command: list[str], cwd: Path, timeout_seconds: int) -> subprocess.CompletedProcess[str]:
        return subprocess.CompletedProcess(command, 0, stdout="ok", stderr="")

    @staticmethod
    def _failure(command: list[str], cwd: Path, timeout_seconds: int) -> subprocess.CompletedProcess[str]:
        return subprocess.CompletedProcess(command, 1, stdout="", stderr="error")

    @staticmethod
    def _timeout(command: list[str], cwd: Path, timeout_seconds: int) -> subprocess.CompletedProcess[str]:
        raise subprocess.TimeoutExpired(command, timeout_seconds, output="out", stderr="err")

    @staticmethod
    def _unexpected(command: list[str], cwd: Path, timeout_seconds: int) -> subprocess.CompletedProcess[str]:
        raise AssertionError("lake build should not run for prohibited placeholders")


if __name__ == "__main__":
    unittest.main()
