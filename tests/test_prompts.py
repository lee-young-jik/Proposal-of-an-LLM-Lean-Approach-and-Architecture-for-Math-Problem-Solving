from __future__ import annotations

from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from single_orchestrator.prompts import PromptRegistry


class PromptRegistryTest(unittest.TestCase):
    def test_build_from_state_uses_only_whitelisted_fields(self) -> None:
        registry = PromptRegistry.defaults()
        prompt = registry.build_from_state(
            "lean_generator.generate",
            {
                "problem": "prove 1 = 1",
                "current_informal": "by reflexivity",
                "formal_statement": "theorem target : 1 = 1 := by",
                "allowed_imports": ["Mathlib"],
                "lean_header": "import Mathlib\n\nopen scoped BigOperators",
                "lean_error_log": "SECRET_ERROR",
            },
        )

        self.assertEqual(
            set(prompt.inputs),
            {
                "problem",
                "current_informal",
                "formal_statement",
                "allowed_imports",
                "lean_header",
            },
        )
        self.assertIn("theorem target : 1 = 1 := by", prompt.text)
        self.assertIn("Mathlib", prompt.text)
        self.assertIn("open scoped BigOperators", prompt.text)
        self.assertNotIn("SECRET_ERROR", prompt.text)

    def test_build_rejects_non_whitelisted_fields(self) -> None:
        registry = PromptRegistry.defaults()

        with self.assertRaises(ValueError):
            registry.build(
                "lean_generator.generate",
                problem="prove 1 = 1",
                current_informal="by reflexivity",
                formal_statement="theorem target : 1 = 1 := by",
                allowed_imports=["Mathlib"],
                lean_header="import Mathlib",
                lean_error_log="SECRET_ERROR",
            )

    def test_single_orchestrator_prompt_receives_lean_header(self) -> None:
        registry = PromptRegistry.defaults()
        prompt = registry.build(
            "orchestrator.strategy",
            problem="prove True",
            lean_header="import Mathlib\n\nopen scoped BigOperators",
        )

        self.assertEqual(set(prompt.inputs), {"problem", "lean_header"})
        self.assertIn("Lean header", prompt.text)
        self.assertIn("open scoped BigOperators", prompt.text)

    def test_single_false_decision_prompt_is_conservative(self) -> None:
        registry = PromptRegistry.defaults()
        prompt = registry.build(
            "orchestrator.false_decision",
            problem="prove False",
            formal_statement="theorem target : False := by",
            lean_header="import Mathlib",
            strategy="Try contradiction.",
            trial_memory=[],
        )

        self.assertEqual(prompt.version, "v7")
        self.assertIn("there are no hidden premises", prompt.text)
        self.assertIn("Be extremely conservative", prompt.text)
        self.assertIn("failed proof attempts", prompt.text)
        self.assertIn("clear mathematical refutation", prompt.text)
        self.assertIn("Counterexample evidence may appear", prompt.text)
        self.assertIn("judge the exact Lean target", prompt.text)
        self.assertIn("clear_counterexample", prompt.text)
        self.assertIn("clear_negation", prompt.text)
        self.assertIn("output categories you assign", prompt.text)
        self.assertIn("do not expect these category names to appear literally", prompt.text)
        self.assertIn("explicit contradiction", prompt.text)
        self.assertIn("explicit_contradiction", prompt.text)
        self.assertIn("even slightly unclear", prompt.text)
        self.assertIn("exact target is false", prompt.text)
        self.assertIn("formal statement", prompt.text)
        self.assertIn("never false", prompt.text)

    def test_lean_generator_prompt_forbids_placeholders(self) -> None:
        registry = PromptRegistry.defaults()
        prompt = registry.build(
            "lean_generator.generate",
            problem="prove True",
            current_informal="trivial",
            formal_statement="theorem target : True := by",
            allowed_imports=["Mathlib.Init"],
            lean_header="import Mathlib.Init",
            lean_context="Verified import candidates:\n- import Mathlib.Init",
        )

        self.assertEqual(prompt.version, "v4")
        self.assertIn("Never use `sorry`, `admit`, `axiom`", prompt.text)
        self.assertIn("complete proof", prompt.text)
        self.assertIn("Allowed imports", prompt.text)
        self.assertIn("avoid broad `import Mathlib`", prompt.text)
        self.assertIn("Mathlib.Init", prompt.text)
        self.assertIn("Lean header", prompt.text)
        self.assertIn("Lean environment guardrails", prompt.text)
        self.assertIn("Verified import candidates", prompt.text)
        self.assertIn("Mathlib naming discipline", prompt.text)
        self.assertIn("theorem and lemma names are usually snake_case", prompt.text)
        self.assertIn("Do not assume a declaration is in the `Complex` namespace", prompt.text)
        self.assertIn("Unknown identifier", prompt.text)
        self.assertIn("Do not run shell commands", prompt.text)
        self.assertIn("interval_cases n <;> simp_all", prompt.text)

    def test_dual_truth_lean_generator_prompt_includes_mathlib_naming_discipline(self) -> None:
        registry = PromptRegistry.defaults()
        prompt = registry.build(
            "truth_lean_generator.generate",
            problem="prove True",
            current_informal="trivial",
            formal_statement="theorem target : True := by",
            allowed_imports=["Mathlib.Init"],
            lean_header="import Mathlib.Init",
        )

        self.assertEqual(prompt.version, "v4")
        self.assertIn("Mathlib naming discipline", prompt.text)
        self.assertIn("avoid broad `import Mathlib`", prompt.text)
        self.assertIn("theorem and lemma names are usually snake_case", prompt.text)
        self.assertIn("If the exact Mathlib name is uncertain", prompt.text)
        self.assertIn("Do not run shell commands", prompt.text)
        self.assertIn("Truth-lane repair discipline", prompt.text)
        self.assertIn("prioritize repairing the exact reported Lean failure", prompt.text)
        self.assertIn("Do not discuss counterexamples", prompt.text)
        self.assertIn("No goals to be solved", prompt.text)
        self.assertIn("remove the extra cleanup tactic", prompt.text)
        self.assertIn("interval_cases n <;> simp_all", prompt.text)
        self.assertIn("Avoid broad `norm_num at h ⊢`", prompt.text)
        self.assertIn("timed-out Lean proof used `linarith`", prompt.text)
        self.assertIn("For `Real.log` or logarithm proofs", prompt.text)
        self.assertIn("do not use `linarith` or `nlinarith` anywhere", prompt.text)
        self.assertIn("rejected before Lean runs", prompt.text)
        self.assertIn("Do not use `Real.logb`", prompt.text)
        self.assertIn("naturals coerced to reals", prompt.text)
        self.assertIn("(div_eq_iff h).mp", prompt.text)

    def test_empty_optional_lean_context_is_omitted(self) -> None:
        registry = PromptRegistry.defaults()
        prompt = registry.build(
            "truth_lean_generator.generate",
            problem="prove True",
            current_informal="trivial",
            formal_statement="theorem target : True := by",
            allowed_imports=[],
            lean_header="",
        )

        self.assertNotIn("Allowed imports, if provided", prompt.text)
        self.assertNotIn("Lean header, if provided", prompt.text)

    def test_dual_falsity_lean_generator_prompt_exists(self) -> None:
        registry = PromptRegistry.defaults()

        prompt = registry.build(
            "falsity_lean_generator.generate",
            problem="prove True",
            current_informal="trivial",
            formal_statement="theorem target : True := by",
            allowed_imports=["Mathlib.Init"],
            lean_header="import Mathlib.Init",
        )

        self.assertIn("Import discipline", prompt.text)
        self.assertIn("Previous trial feedback", prompt.text)

        with self.assertRaises(KeyError):
            registry.build(
                "falsity_retry_planner.plan",
                problem="prove True",
                failure_context={},
            )

    def test_retry_planner_prompt_forbids_axiom_retry_plans(self) -> None:
        registry = PromptRegistry.defaults()
        prompt = registry.build(
            "retry_planner.plan",
            problem="prove True",
            failure_context={
                "failure_reason": "Lean build failed.",
                "informal": "Use a theorem.",
                "formal_state": "axiom missing : True",
                "lean_error_log": (
                    "Generated Lean contains a prohibited placeholder: sorry/admit/axiom."
                ),
            },
        )

        self.assertEqual(prompt.version, "v3")
        self.assertIn("prohibited placeholders", prompt.text)
        self.assertIn("Do not recommend axioms", prompt.text)

    def test_nature_initial_prompt_has_no_empty_retry_fields(self) -> None:
        registry = PromptRegistry.defaults()
        prompt = registry.build(
            "nature_agent.initial",
            problem="prove True",
            strategy="Use trivial.",
        )

        self.assertEqual(prompt.version, "v2")
        self.assertEqual(set(prompt.inputs), {"problem", "strategy"})
        self.assertNotIn("trial_index", prompt.inputs)
        self.assertNotIn("previous_trial", prompt.inputs)
        self.assertNotIn("Previous trial memory", prompt.text)
        self.assertIn("write the proof as a mathematician would", prompt.text)
        self.assertIn("Do not write Lean code", prompt.text)

    def test_nature_retry_prompt_carries_only_previous_trial_memory(self) -> None:
        registry = PromptRegistry.defaults()
        prompt = registry.build(
            "nature_agent.retry",
            problem="prove True",
            strategy="Use trivial.",
            previous_trial={"lean_error_log": "error", "retry_plan": "fix it"},
        )

        self.assertEqual(prompt.version, "v2")
        self.assertEqual(set(prompt.inputs), {"problem", "strategy", "previous_trial"})
        self.assertNotIn("trial_index", prompt.inputs)
        self.assertIn("Previous trial memory", prompt.text)
        self.assertIn("Do not write Lean code", prompt.text)

    def test_dual_falsity_prompts_do_not_allow_truth_concession(self) -> None:
        registry = PromptRegistry.defaults()

        truth = registry.build(
            "dual_orchestrator.truth_strategy",
            problem="prove True",
            formal_statement="theorem target : True := by",
            lean_header="import Mathlib",
            round_summaries=[],
        )
        strategy = registry.build(
            "dual_orchestrator.falsity_strategy",
            problem="prove True",
            formal_statement="theorem target : True := by",
            lean_header="import Mathlib",
            round_summaries=[],
        )
        opinion = registry.build(
            "falsity_nature_agent.initial",
            problem="prove True",
            strategy="Attack the theorem.",
        )

        self.assertEqual(truth.version, "v2")
        self.assertEqual(strategy.version, "v2")
        self.assertEqual(opinion.version, "v2")
        self.assertIn("must assume the theorem is true as a role assignment", truth.text)
        self.assertIn("must not evaluate whether the statement is actually true", truth.text)
        self.assertIn("must never conclude that the theorem is true", strategy.text)
        self.assertIn("Never conclude that the statement is true", opinion.text)
        self.assertIn("If one attack fails", strategy.text)
        self.assertIn("next strongest attack", opinion.text)

    def test_dual_decision_prompt_only_judges_falsity(self) -> None:
        registry = PromptRegistry.defaults()
        prompt = registry.build(
            "dual_orchestrator.decision",
            problem="prove True",
            formal_statement="theorem target : True := by",
            lean_header="import Mathlib",
            truth_memory=[],
            falsity_memory=[],
        )

        self.assertEqual(prompt.version, "v6")
        self.assertIn("there are no hidden premises", prompt.text)
        self.assertIn("falsity only", prompt.text)
        self.assertIn("Do not decide that the theorem is true", prompt.text)
        self.assertIn("role assumptions", prompt.text)
        self.assertIn("not as facts", prompt.text)
        self.assertIn("not treat either role assumption as evidence", prompt.text)
        self.assertIn("clear mathematical refutation", prompt.text)
        self.assertIn("Counterexample evidence may appear", prompt.text)
        self.assertIn("judge the exact Lean target", prompt.text)
        self.assertIn("clear_counterexample", prompt.text)
        self.assertIn("clear_negation", prompt.text)
        self.assertIn("explicit_contradiction", prompt.text)
        self.assertIn("output categories you assign", prompt.text)
        self.assertIn("do not expect these category names to appear literally", prompt.text)
        self.assertIn("even slightly unclear", prompt.text)
        self.assertIn("confused, uncertain", prompt.text)
        self.assertIn("exact target is false", prompt.text)
        self.assertIn("formal statement", prompt.text)
        self.assertIn("decision must be one of false, continue, unknown", prompt.text)


if __name__ == "__main__":
    unittest.main()
