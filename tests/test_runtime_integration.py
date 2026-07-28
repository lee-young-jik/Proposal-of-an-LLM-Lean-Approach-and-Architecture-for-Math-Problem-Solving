from __future__ import annotations

from pathlib import Path
import json
import shutil
import sys
import tempfile
import threading
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from single_orchestrator.memory import JsonlTrialMemory
from single_orchestrator.model import (
    CodexCliModelClient,
    ModelClientError,
    OpenAICompatibleModelClient,
    PromptRoutingModelClient,
    make_default_model_client,
)
from single_orchestrator.prompts import BuiltPrompt, PromptRegistry
from single_orchestrator.dual_runtime import DualOrchestrator, DualOrchestratorRuntime
from single_orchestrator.runtime import SingleOrchestrator, SingleOrchestratorRuntime
from single_orchestrator.verifier import LakeVerifier


ROOT = Path(__file__).resolve().parents[1]
LEGACY_FALSE_PROTOCOL = (
    "Legacy test predates the exact False Reasoner/private-key review protocol."
)


class FakeModelClient:
    def __init__(self, responses: dict[str, str | Exception | list[str | Exception]]):
        self.responses = {
            key: ([value] if isinstance(value, str) else list(value))
            for key, value in responses.items()
        }
        self.calls: list[BuiltPrompt] = []

    def complete(self, prompt: BuiltPrompt) -> str:
        self.calls.append(prompt)
        if prompt.name == "correction_judge.compare" and prompt.name not in self.responses:
            expected = prompt.inputs.get("expected_correction", "").strip()
            proposed = prompt.inputs.get("proposed_correction", "").strip()
            return json.dumps(
                {
                    "equivalent": bool(expected) and expected == proposed,
                    "evidence_supported": bool(expected) and expected == proposed,
                    "uncertainties": [],
                    "rationale": (
                        "Mock corrections match exactly."
                        if expected == proposed
                        else "Mock corrections do not match."
                    ),
                }
            )
        if prompt.name in {
            "false_judgment_agent.assess",
            "orchestrator.false_judgment_review",
        } and prompt.name not in self.responses:
            return json.dumps(
                {
                    "decision": "continue",
                    "rationale": "No mocked false judgment.",
                    "false_evidence": "none",
                    "correction_to_true": "",
                }
            )
        values = self.responses[prompt.name]
        if isinstance(values[0], Exception):
            raise values.pop(0)
        if len(values) > 1:
            return values.pop(0)
        return values[0]


class ConstantModelClient:
    def __init__(self, response: str):
        self.response = response
        self.calls: list[BuiltPrompt] = []

    def complete(self, prompt: BuiltPrompt) -> str:
        self.calls.append(prompt)
        return self.response


class DelayedStrategyModelClient:
    def __init__(self, delay_seconds: float = 0.2):
        self.delay_seconds = delay_seconds
        self.calls: list[BuiltPrompt] = []
        self.intervals: dict[str, tuple[float, float]] = {}
        self._lock = threading.Lock()

    def complete(self, prompt: BuiltPrompt) -> str:
        started = time.monotonic()
        with self._lock:
            self.calls.append(prompt)
        if prompt.name in {
            "dual_orchestrator.truth_strategy",
            "dual_orchestrator.falsity_strategy",
        }:
            time.sleep(self.delay_seconds)
        ended = time.monotonic()
        with self._lock:
            self.intervals[prompt.name] = (started, ended)
        return f"{prompt.name} response"


@unittest.skipUnless(shutil.which("lake"), "lake is required for integration tests")
class RuntimeIntegrationTest(unittest.TestCase):
    def test_extract_core_lean_error_log_keeps_diagnostics_without_lake_noise(self) -> None:
        raw_log = "\n".join(
            [
                "✖ [2016/2016] Building LeanMath.Scratch.Generated (13s)",
                "trace: .> LEAN_PATH=/very/long/path lake env lean Generated.lean --json",
                "error: LeanMath/Scratch/Generated.lean:3:45: failed to synthesize instance of type class",
                "  AddCommMonoid ℂ",
                "",
                "Hint: Type class instance resolution failures can be inspected with trace.",
                "error: LeanMath/Scratch/Generated.lean:4:10: failed to synthesize instance of type class",
                "  NontriviallyNormedField ℂ",
                "Some required targets logged failures:",
                "- LeanMath.Scratch.Generated",
                "error: build failed",
            ]
        )

        compact = SingleOrchestratorRuntime._extract_core_lean_error_log(raw_log)

        self.assertIn("✖ [2016/2016] Building LeanMath.Scratch.Generated (13s)", compact)
        self.assertIn("failed to synthesize instance of type class", compact)
        self.assertIn("AddCommMonoid ℂ", compact)
        self.assertIn("NontriviallyNormedField ℂ", compact)
        self.assertNotIn("LEAN_PATH", compact)
        self.assertNotIn("Some required targets logged failures", compact)

    def test_extract_core_lean_error_log_keeps_proof_audit_failure(self) -> None:
        raw_log = "\n".join(
            [
                "✔ [1/1] Built MiniF2F.Scratch.Generated (112s)",
                "Proof audit failed: expected exactly one top-level theorem declaration.",
            ]
        )

        compact = SingleOrchestratorRuntime._extract_core_lean_error_log(raw_log)

        self.assertIn("✔ [1/1] Built MiniF2F.Scratch.Generated (112s)", compact)
        self.assertIn("Proof audit failed: expected exactly one top-level theorem", compact)

    def test_prompt_routing_model_client_uses_prompt_specific_clients(self) -> None:
        default = ConstantModelClient("default")
        orchestrator = ConstantModelClient("orchestrator")
        lean = ConstantModelClient("lean")
        router = PromptRoutingModelClient(
            default_client=default,
            prompt_clients={
                "orchestrator.strategy": orchestrator,
                "lean_generator.generate": lean,
            },
        )

        self.assertEqual(
            router.complete(BuiltPrompt("orchestrator.strategy", "v1", {}, "")),
            "orchestrator",
        )
        self.assertEqual(
            router.complete(BuiltPrompt("lean_generator.generate", "v1", {}, "")),
            "lean",
        )
        self.assertEqual(
            router.complete(BuiltPrompt("nature_agent.initial", "v1", {}, "")),
            "default",
        )
        self.assertEqual(len(orchestrator.calls), 1)
        self.assertEqual(len(lean.calls), 1)
        self.assertEqual(len(default.calls), 1)

    def test_strict_prompt_routing_rejects_unmapped_prompt(self) -> None:
        router = PromptRoutingModelClient(
            default_client=ConstantModelClient("default"),
            prompt_clients={},
            strict=True,
        )

        with self.assertRaisesRegex(ModelClientError, "No model route configured"):
            router.complete(BuiltPrompt("unmapped.prompt", "v1", {}, ""))

    def test_codex_cli_error_is_compacted_before_retry_context(self) -> None:
        raw = "\n".join(
            [
                "Reading additional input from stdin...",
                "2026-07-02 WARN codex_features: unknown feature key",
                "System:",
                "very long prompt body that should not be replayed",
                "ERROR: Codex ran out of room in the model's context window. Start a new thread.",
                "tokens used",
                "0",
            ]
        )

        compact = CodexCliModelClient._compact_codex_error(raw, "")

        self.assertIn("ran out of room", compact)
        self.assertNotIn("very long prompt body", compact)
        self.assertNotIn("System:", compact)

    def test_openrouter_style_model_uses_openai_compatible_client(self) -> None:
        client = make_default_model_client(
            ROOT,
            model="openai/gpt-5.4-nano",
            timeout_seconds=123,
        )

        self.assertIsInstance(client, OpenAICompatibleModelClient)
        self.assertEqual(client.model, "openai/gpt-5.4-nano")
        self.assertEqual(client.timeout_seconds, 123)
        self.assertEqual(client.api_key_env, "OPENROUTER_API_KEY")

    def test_openrouter_prefix_is_stripped_from_model_name(self) -> None:
        client = make_default_model_client(
            ROOT,
            model="openrouter:openai/gpt-5.4-nano",
        )

        self.assertIsInstance(client, OpenAICompatibleModelClient)
        self.assertEqual(client.model, "openai/gpt-5.4-nano")
        self.assertEqual(client.base_url, "https://openrouter.ai/api/v1")
        self.assertEqual(client.api_key_env, "OPENROUTER_API_KEY")

    def test_openai_prefix_uses_openai_api(self) -> None:
        client = make_default_model_client(
            ROOT,
            model="openai:gpt-5.4-nano",
        )

        self.assertIsInstance(client, OpenAICompatibleModelClient)
        self.assertEqual(client.model, "gpt-5.4-nano")
        self.assertEqual(client.base_url, "https://api.openai.com/v1")
        self.assertEqual(client.api_key_env, "OPENAI_API_KEY")

    def test_success_stops_after_first_trial(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            memory = JsonlTrialMemory(Path(raw_dir) / "memory.jsonl")
            fake = FakeModelClient(
                {
                    "orchestrator.strategy": "Use reflexivity.",
                    "nature_agent.initial": "Both sides are definitionally equal.",
                    "lean_generator.generate": (
                        "```lean\n"
                        "theorem generated_example : 1 = 1 := by\n"
                        "  rfl\n"
                        "```"
                    ),
                }
            )
            orchestrator = SingleOrchestrator(
                model_client=fake,
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                memory=memory,
                project_root=ROOT,
            )

            result = orchestrator.run(
                "Prove that 1 equals 1.",
                formal_statement="theorem generated_example : 1 = 1 := by",
            )
            records = memory.load_all()

        self.assertTrue(result["success"])
        self.assertEqual(result["trials"], 1)
        self.assertEqual(len(records), 1)
        lean_prompts = [call for call in fake.calls if call.name == "lean_generator.generate"]
        self.assertNotIn("lean_error_log", lean_prompts[0].inputs)
        self.assertEqual(
            lean_prompts[0].inputs["formal_statement"],
            "theorem generated_example : 1 = 1 := by",
        )

    def test_bare_by_block_is_wrapped_with_formal_statement(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            memory = JsonlTrialMemory(Path(raw_dir) / "memory.jsonl")
            fake = FakeModelClient(
                {
                    "orchestrator.strategy": "Use reflexivity.",
                    "nature_agent.initial": "Both sides are definitionally equal.",
                    "lean_generator.generate": "by\n  rfl",
                }
            )
            orchestrator = SingleOrchestrator(
                model_client=fake,
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                memory=memory,
                project_root=ROOT,
            )

            result = orchestrator.run(
                "Prove that 1 equals 1.",
                formal_statement="theorem generated_example : 1 = 1 := by",
            )

        self.assertTrue(result["success"])
        self.assertTrue(
            result["verifier_result"]["formal_state"].startswith(
                "theorem generated_example : 1 = 1 := by"
            )
        )

    @unittest.skip(LEGACY_FALSE_PROTOCOL)
    def test_restrategy_after_three_failures_returns_to_nature_agent(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            memory = JsonlTrialMemory(Path(raw_dir) / "memory.jsonl")
            fake = FakeModelClient(
                {
                    "orchestrator.strategy": "Try reflexivity.",
                    "nature_agent.initial": "Claim the false equality is reflexive.",
                    "nature_agent.retry": [
                        "Try the same false equality again.",
                        "Try the false equality a third time.",
                        "Use the revised strategy to prove a true equality.",
                    ],
                    "lean_generator.generate": [
                        "theorem generated_bad : 1 = 2 := by\n  rfl",
                        "theorem generated_bad : 1 = 2 := by\n  rfl",
                        "theorem generated_bad : 1 = 2 := by\n  rfl",
                        "theorem generated_good : 1 = 1 := by\n  rfl",
                    ],
                    "retry_planner.plan": [
                        "The equality target is false; change strategy.",
                        "Reflexivity cannot solve this target.",
                        "Third failure triggers a new strategy.",
                    ],
                    "orchestrator.false_decision": json.dumps(
                        {
                            "decision": "continue",
                            "rationale": "No validated counterexample was supplied.",
                            "false_evidence": "none",
                        }
                    ),
                    "orchestrator.restrategy": "Switch to a true equality target.",
                }
            )
            orchestrator = SingleOrchestrator(
                model_client=fake,
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                memory=memory,
                project_root=ROOT,
            )

            result = orchestrator.run("Prove that 1 equals 2.")
            records = memory.load_all()

        self.assertTrue(result["success"])
        self.assertGreaterEqual(result["trials"], 1)
        self.assertGreaterEqual(result["rounds"], 1)
        self.assertGreaterEqual(len(records), 1)
        self.assertEqual(
            set(records[0]),
            {
                "lane",
                "trial_index",
                "informal",
                "formal_state",
                "lean_error_log",
                "retry_plan",
            },
        )
        self.assertEqual(records[0]["lane"], "single")
        self.assertEqual(records[0]["trial_index"], 1)
        call_names = [call.name for call in fake.calls]
        self.assertIn("orchestrator.strategy", call_names)
        self.assertIn("nature_agent.initial", call_names)
        self.assertIn("lean_generator.generate", call_names)
        restrategy_prompts = [
            call for call in fake.calls if call.name == "orchestrator.restrategy"
        ]
        trial_memory = json.loads(restrategy_prompts[0].inputs["trial_memory"])
        self.assertEqual(
            set(trial_memory[0]),
            {"informal", "lean_error_log", "retry_plan"},
        )

    def test_verified_proof_does_not_call_semantic_judge(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            memory = JsonlTrialMemory(Path(raw_dir) / "memory.jsonl")
            fake = FakeModelClient(
                {
                    "orchestrator.strategy": "Prove the requested theorem.",
                    "nature_agent.initial": "Prove the theorem directly.",
                    "lean_generator.generate": "theorem generated_right : True := by\n  trivial",
                }
            )
            orchestrator = SingleOrchestrator(
                model_client=fake,
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                memory=memory,
                project_root=ROOT,
            )

            result = orchestrator.run("Prove True.")
            records = memory.load_all()

        self.assertTrue(result["success"])
        self.assertEqual(result["trials"], 1)
        self.assertEqual(records[0]["lean_error_log"], "")
        self.assertNotIn("llm_judge.proofnet_equivalence", [call.name for call in fake.calls])

    def test_lean_generation_model_error_is_recorded_as_retryable_failure(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            memory = JsonlTrialMemory(Path(raw_dir) / "memory.jsonl")
            fake = FakeModelClient(
                {
                    "orchestrator.strategy": "Try a direct proof.",
                    "nature_agent.initial": "First informal proof.",
                    "nature_agent.retry": "Second informal proof.",
                    "lean_generator.generate": [
                        ModelClientError("codex exec timed out after 300 seconds"),
                        "theorem generated_good : True := by\n  trivial",
                    ],
                    "retry_planner.plan": "Regenerate concise Lean code.",
                }
            )
            orchestrator = SingleOrchestrator(
                model_client=fake,
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                memory=memory,
                project_root=ROOT,
            )

            result = orchestrator.run("Prove True.")
            records = memory.load_all()

        self.assertTrue(result["success"])
        self.assertEqual(result["trials"], 2)
        self.assertIn("Lean generation model failed", records[0]["lean_error_log"])
        self.assertEqual(records[0]["formal_state"], "")
        self.assertIn("Regenerate concise Lean code.", records[0]["retry_plan"])
        retry_prompts = [call for call in fake.calls if call.name == "nature_agent.retry"]
        previous_trial = json.loads(retry_prompts[0].inputs["previous_trial"])
        self.assertEqual(
            set(previous_trial),
            {"lean_error_log", "retry_plan"},
        )
        self.assertNotIn("formal_state", previous_trial)
        planner_prompts = [call for call in fake.calls if call.name == "retry_planner.plan"]
        self.assertIn("failure_context", planner_prompts[0].inputs)
        failure_context = json.loads(planner_prompts[0].inputs["failure_context"])
        self.assertEqual(
            failure_context["failure_reason"],
            "Lean generation model timed out before producing Lean code.",
        )
        self.assertNotIn("formal_state", failure_context)

    def test_retry_planner_model_error_does_not_abort_budget(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            memory = JsonlTrialMemory(Path(raw_dir) / "memory.jsonl")
            fake = FakeModelClient(
                {
                    "orchestrator.strategy": "Try a direct proof.",
                    "nature_agent.initial": "First informal proof.",
                    "nature_agent.retry": "Second informal proof.",
                    "lean_generator.generate": [
                        "theorem generated_bad : 1 = 2 := by\n  rfl",
                        "theorem generated_good : True := by\n  trivial",
                    ],
                    "retry_planner.plan": [
                        ModelClientError(
                            "codex exec failed for retry_planner.plan: ERROR: Codex ran out of room"
                        )
                    ],
                }
            )
            orchestrator = SingleOrchestrator(
                model_client=fake,
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                memory=memory,
                project_root=ROOT,
            )

            result = orchestrator.run("Recover after retry planner failure.")
            records = memory.load_all()

        self.assertTrue(result["success"])
        self.assertEqual(result["trials"], 2)
        self.assertIn("Retry planner failed", records[0]["retry_plan"])

    def test_full_failure_budget_does_not_hit_langgraph_recursion_limit(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            memory = JsonlTrialMemory(Path(raw_dir) / "memory.jsonl")
            fake = FakeModelClient(
                {
                    "orchestrator.strategy": "Try a proof.",
                    "nature_agent.initial": "Try reflexivity on the false equality.",
                    "nature_agent.retry": "Try reflexivity on the false equality.",
                    "lean_generator.generate": "theorem generated_bad : 1 = 2 := by\n  rfl",
                    "retry_planner.plan": "The target is still false.",
                    "orchestrator.false_decision": json.dumps(
                        {
                            "decision": "continue",
                            "rationale": "Repeated failures are not validated false evidence.",
                            "false_evidence": "none",
                        }
                    ),
                    "orchestrator.restrategy": "Try another strategy, but keep the cap finite.",
                }
            )
            orchestrator = SingleOrchestrator(
                model_client=fake,
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                memory=memory,
                project_root=ROOT,
                max_trials=2,
                max_strategy_rounds=3,
            )

            result = orchestrator.run("Exercise the full failure budget.")
            records = memory.load_all()

        self.assertFalse(result["success"])
        self.assertEqual(result["trials"], 6)
        self.assertEqual(result["rounds"], 3)
        self.assertEqual(len(records), 6)
        self.assertEqual(result["final_status"], "not_solved")

    @unittest.skip(LEGACY_FALSE_PROTOCOL)
    def test_single_false_decision_after_failed_round_stops_as_false(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            memory = JsonlTrialMemory(Path(raw_dir) / "memory.jsonl")
            fake = FakeModelClient(
                {
                    "orchestrator.strategy": "Try to prove the target.",
                    "nature_agent.initial": "Attempt the proof.",
                    "nature_agent.retry": "Retry the proof.",
                    "lean_generator.generate": "theorem generated_bad : 1 = 2 := by\n  rfl",
                    "retry_planner.plan": "The generated proof fails.",
                    "false_judgment_agent.assess": json.dumps(
                        {
                            "decision": "false",
                            "rationale": (
                                "The exact statement asserts 1 = 2, but Nat numerals "
                                "one and two are distinct."
                            ),
                            "false_evidence": "validated_counterexample",
                            "correction_to_true": "change conclusion from 1 = 2 to 1 ≠ 2",
                            "hypotheses_check": "The empty hypotheses are satisfiable.",
                            "conclusion_check": "Nat.one_ne_bit0 proves the numerals differ.",
                            "uncertainties": [],
                        }
                    ),
                    "orchestrator.false_decision": json.dumps(
                        {
                            "decision": "false",
                            "rationale": "The exact statement is refuted by distinct numerals.",
                            "false_evidence": "validated_counterexample",
                            "correction_to_true": "change conclusion from 1 = 2 to 1 ≠ 2",
                            "validation_complete": True,
                            "hypotheses_verified": True,
                            "conclusion_falsified": True,
                            "uncertainties": [],
                        }
                    ),
                }
            )
            orchestrator = SingleOrchestrator(
                model_client=fake,
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                memory=memory,
                project_root=ROOT,
                max_trials=3,
                max_strategy_rounds=3,
            )

            result = orchestrator.run(
                "Prove that 1 equals 2.",
                expected_false_fix=["change conclusion from 1 = 2 to 1 ≠ 2"],
            )

        self.assertFalse(result["success"])
        self.assertEqual(result["final_status"], "false")
        self.assertEqual(result["trials"], 3)
        self.assertEqual(result["false_evidence"], "validated_counterexample")
        self.assertIn("exact statement", result["rationale"])
        self.assertNotIn("orchestrator.restrategy", [call.name for call in fake.calls])

    @unittest.skip(LEGACY_FALSE_PROTOCOL)
    def test_single_false_decision_requires_validated_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            fake = FakeModelClient(
                {
                    "false_judgment_agent.assess": json.dumps(
                        {
                            "decision": "false",
                            "rationale": "The proof failed many times.",
                            "false_evidence": "none",
                        }
                    ),
                    "orchestrator.false_decision": json.dumps(
                        {
                            "decision": "continue",
                            "rationale": "The proof failed, but no refutation was supplied.",
                            "false_evidence": "none",
                        }
                    ),
                }
            )
            runtime = SingleOrchestratorRuntime(
                model_client=fake,
                prompts=PromptRegistry.defaults(),
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                memory=JsonlTrialMemory(Path(raw_dir) / "memory.jsonl"),
            )

            update = runtime.decide_false_after_round(
                {
                    "problem": "A hard problem.",
                    "formal_statement": "theorem hard : False := by",
                    "strategy": "Try direct proof.",
                    "trial_memory": [],
                    "strategy_round": 1,
                }
            )

        self.assertFalse(update["done"])
        self.assertTrue(update["needs_restrategy"])
        self.assertEqual(update["false_evidence"], "none")
        self.assertIn("proof failed", update["false_rationale"])

    @unittest.skip(LEGACY_FALSE_PROTOCOL)
    def test_single_false_decision_accepts_explicit_contradiction(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            fake = FakeModelClient(
                {
                    "false_judgment_agent.assess": json.dumps(
                        {
                            "decision": "false",
                            "rationale": (
                                "The exact target requires proving `True ∧ False`; "
                                "the second conjunct is impossible under the satisfiable "
                                "empty context."
                            ),
                            "false_evidence": "explicit_contradiction",
                            "correction_to_true": "remove the False conjunct",
                            "hypotheses_check": "The empty context is satisfiable.",
                            "conclusion_check": "The False conjunct cannot be inhabited.",
                            "uncertainties": [],
                        }
                    ),
                    "orchestrator.false_decision": json.dumps(
                        {
                            "decision": "false",
                            "rationale": "The exact target contains an impossible False conjunct.",
                            "false_evidence": "explicit_contradiction",
                            "correction_to_true": "remove the False conjunct",
                            "validation_complete": True,
                            "hypotheses_verified": True,
                            "conclusion_falsified": True,
                            "uncertainties": [],
                        }
                    ),
                }
            )
            runtime = SingleOrchestratorRuntime(
                model_client=fake,
                prompts=PromptRegistry.defaults(),
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                memory=JsonlTrialMemory(Path(raw_dir) / "memory.jsonl"),
            )

            update = runtime.decide_false_after_round(
                {
                    "problem": "Prove True and False.",
                    "formal_statement": "theorem impossible : True ∧ False := by",
                    "strategy": "Try direct proof.",
                    "trial_memory": [],
                    "strategy_round": 1,
                    "expected_false_fix": ["remove the False conjunct"],
                }
            )

        self.assertTrue(update["done"])
        self.assertEqual(update["final_status"], "false")
        self.assertEqual(update["false_evidence"], "explicit_contradiction")

    @unittest.skip(LEGACY_FALSE_PROTOCOL)
    def test_single_false_decision_accepts_clear_counterexample(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            fake = FakeModelClient(
                {
                    "false_judgment_agent.assess": json.dumps(
                        {
                            "decision": "false",
                            "rationale": (
                                "The accumulated memory identifies the concrete instance "
                                "n = 0, where the exact target `0 > 1` is false."
                            ),
                            "false_evidence": "clear_counterexample",
                            "correction_to_true": "add hypothesis n ≠ 0",
                            "hypotheses_check": "n = 0 satisfies the unrestricted hypotheses.",
                            "conclusion_check": "At n = 0, the conclusion is 0 > 1.",
                            "uncertainties": [],
                        }
                    ),
                    "orchestrator.false_decision": json.dumps(
                        {
                            "decision": "false",
                            "rationale": "The concrete instance n = 0 refutes the exact target.",
                            "false_evidence": "clear_counterexample",
                            "correction_to_true": "add hypothesis n ≠ 0",
                            "validation_complete": True,
                            "hypotheses_verified": True,
                            "conclusion_falsified": True,
                            "uncertainties": [],
                        }
                    ),
                }
            )
            runtime = SingleOrchestratorRuntime(
                model_client=fake,
                prompts=PromptRegistry.defaults(),
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                memory=JsonlTrialMemory(Path(raw_dir) / "memory.jsonl"),
            )

            update = runtime.decide_false_after_round(
                {
                    "problem": "Prove every natural number is greater than one.",
                    "formal_statement": "theorem bad (n : Nat) : n > 1 := by",
                    "strategy": "Try direct proof.",
                    "trial_memory": [
                        {
                            "informal": "At n = 0 the target becomes 0 > 1, false.",
                            "lean_error_log": "",
                            "retry_plan": "",
                        }
                    ],
                    "strategy_round": 1,
                    "expected_false_fix": ["add hypothesis n ≠ 0"],
                }
            )

        self.assertTrue(update["done"])
        self.assertEqual(update["final_status"], "false")
        self.assertEqual(update["false_evidence"], "clear_counterexample")

    @unittest.skip(LEGACY_FALSE_PROTOCOL)
    def test_single_blind_false_decision_uses_independent_review(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            fake = FakeModelClient(
                {
                    "false_judgment_agent.assess": json.dumps(
                        {
                            "decision": "unknown",
                            "rationale": "The preliminary agent is uncertain.",
                            "false_evidence": "none",
                            "correction_to_true": "",
                        }
                    ),
                    "orchestrator.false_decision": json.dumps(
                        {
                            "decision": "false",
                            "rationale": (
                                "For x = 1 and y = 1/2, the exact target falsely "
                                "claims that their reduced denominators are equal."
                            ),
                            "false_evidence": "clear_counterexample",
                            "correction_to_true": "add the missing hypothesis on x and y",
                        }
                    ),
                }
            )
            runtime = SingleOrchestratorRuntime(
                model_client=fake,
                prompts=PromptRegistry.defaults(),
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                memory=JsonlTrialMemory(Path(raw_dir) / "memory.jsonl"),
            )

            update = runtime.decide_false_after_round(
                {
                    "problem": "A statement whose informal version has an extra premise.",
                    "formal_statement": "theorem bad (x y : Rat) : x.den = y.den := by",
                    "strategy": "Try a direct proof.",
                    "trial_memory": [],
                    "strategy_round": 1,
                }
            )

        self.assertTrue(update["done"])
        self.assertEqual(update["final_status"], "false")
        self.assertEqual(update["false_evidence"], "clear_counterexample")
        self.assertIn("orchestrator.false_decision", [call.name for call in fake.calls])

    @unittest.skip(LEGACY_FALSE_PROTOCOL)
    def test_single_false_decision_does_not_expose_expected_correction(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            fake = FakeModelClient(
                {
                    "false_judgment_agent.assess": json.dumps(
                        {
                            "decision": "false",
                            "rationale": "The counterexample is n = 0.",
                            "false_evidence": "clear_counterexample",
                            "correction_to_true": "add hypothesis n ≠ 1",
                        }
                    ),
                    "orchestrator.false_decision": json.dumps(
                        {
                            "decision": "continue",
                            "rationale": "The proposed correction is not supported by the evidence.",
                            "false_evidence": "clear_counterexample",
                            "correction_to_true": "add hypothesis n ≠ 1",
                        }
                    ),
                }
            )
            runtime = SingleOrchestratorRuntime(
                model_client=fake,
                prompts=PromptRegistry.defaults(),
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                memory=JsonlTrialMemory(Path(raw_dir) / "memory.jsonl"),
            )

            update = runtime.decide_false_after_round(
                {
                    "problem": "Prove every natural number is greater than one.",
                    "formal_statement": "theorem bad (n : Nat) : n > 1 := by",
                    "strategy": "Try direct proof.",
                    "trial_memory": [],
                    "strategy_round": 1,
                    "expected_false_fix": ["add hypothesis n ≠ 0"],
                }
            )

        self.assertFalse(update["done"])
        self.assertEqual(update["false_evidence"], "clear_counterexample")
        self.assertIn("not supported", update["false_rationale"])
        decision_prompt = next(
            call for call in fake.calls if call.name == "orchestrator.false_decision"
        )
        self.assertNotIn("expected_correction", decision_prompt.inputs)

    @unittest.skip(LEGACY_FALSE_PROTOCOL)
    def test_dual_false_decision_requires_validated_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            fake = FakeModelClient(
                {
                    "false_judgment_agent.assess": json.dumps(
                        {
                            "decision": "false",
                            "rationale": "Many attempts failed, so maybe false.",
                            "false_evidence": "none",
                        }
                    ),
                    "dual_orchestrator.decision": json.dumps(
                        {
                            "decision": "continue",
                            "rationale": "Many attempts failed without a counterexample.",
                            "false_evidence": "none",
                        }
                    ),
                }
            )
            runtime = DualOrchestratorRuntime(
                model_client=fake,
                prompts=PromptRegistry.defaults(),
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                truth_memory=JsonlTrialMemory(Path(raw_dir) / "truth.jsonl"),
                falsity_memory=JsonlTrialMemory(Path(raw_dir) / "falsity.jsonl"),
            )

            decision = runtime.decide(
                problem="A hard problem.",
                formal_statement="theorem hard : False := by",
                truth_memory=[],
                falsity_memory=[],
            )

        self.assertEqual(decision["decision"], "continue")
        self.assertEqual(decision["false_evidence"], "none")
        self.assertIn("Many attempts failed", decision["rationale"])

    @unittest.skip(LEGACY_FALSE_PROTOCOL)
    def test_dual_false_decision_accepts_clear_counterexample(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            fake = FakeModelClient(
                {
                    "false_judgment_agent.assess": json.dumps(
                        {
                            "decision": "false",
                            "rationale": (
                                "The memories identify the concrete instance n = 0, "
                                "where the exact target `0 > 1` is false. This is "
                                "independent of either lane's role assumption."
                            ),
                            "false_evidence": "clear_counterexample",
                            "correction_to_true": "add hypothesis n ≠ 0",
                            "hypotheses_check": "n = 0 satisfies the unrestricted hypotheses.",
                            "conclusion_check": "At n = 0, the conclusion is 0 > 1.",
                            "uncertainties": [],
                        }
                    ),
                    "dual_orchestrator.decision": json.dumps(
                        {
                            "decision": "false",
                            "rationale": "The concrete instance n = 0 refutes the exact target.",
                            "false_evidence": "clear_counterexample",
                            "correction_to_true": "add hypothesis n ≠ 0",
                            "validation_complete": True,
                            "hypotheses_verified": True,
                            "conclusion_falsified": True,
                            "uncertainties": [],
                        }
                    ),
                }
            )
            runtime = DualOrchestratorRuntime(
                model_client=fake,
                prompts=PromptRegistry.defaults(),
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                truth_memory=JsonlTrialMemory(Path(raw_dir) / "truth.jsonl"),
                falsity_memory=JsonlTrialMemory(Path(raw_dir) / "falsity.jsonl"),
            )

            decision = runtime.decide(
                problem="Prove every natural number is greater than one.",
                formal_statement="theorem bad (n : Nat) : n > 1 := by",
                truth_memory=[
                    {
                        "informal": "Truth lane tries to prove the statement by role.",
                        "lean_error_log": "",
                    }
                ],
                falsity_memory=[
                    {
                        "informal": "At n = 0 the target becomes 0 > 1, false.",
                        "lean_error_log": "",
                    }
                ],
                expected_false_fix=["add hypothesis n ≠ 0"],
            )

        self.assertEqual(decision["decision"], "false")
        self.assertEqual(decision["false_evidence"], "clear_counterexample")

    @unittest.skip(LEGACY_FALSE_PROTOCOL)
    def test_dual_blind_false_decision_uses_independent_review(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            fake = FakeModelClient(
                {
                    "false_judgment_agent.assess": json.dumps(
                        {
                            "decision": "unknown",
                            "rationale": "The preliminary agent is uncertain.",
                            "false_evidence": "none",
                            "correction_to_true": "",
                        }
                    ),
                    "dual_orchestrator.decision": json.dumps(
                        {
                            "decision": "false",
                            "rationale": "The falsity lane gives the concrete counterexample n = 0.",
                            "false_evidence": "clear_counterexample",
                            "correction_to_true": "add hypothesis n > 1",
                        }
                    ),
                }
            )
            runtime = DualOrchestratorRuntime(
                model_client=fake,
                prompts=PromptRegistry.defaults(),
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                truth_memory=JsonlTrialMemory(Path(raw_dir) / "truth.jsonl"),
                falsity_memory=JsonlTrialMemory(Path(raw_dir) / "falsity.jsonl"),
            )

            decision = runtime.decide(
                problem="Prove every natural number is greater than one.",
                formal_statement="theorem bad (n : Nat) : n > 1 := by",
                truth_memory=[],
                falsity_memory=[
                    {
                        "informal": "At n = 0 the exact target becomes 0 > 1.",
                        "lean_error_log": "",
                    }
                ],
            )

        self.assertEqual(decision["decision"], "false")
        self.assertEqual(decision["false_evidence"], "clear_counterexample")
        self.assertIn("dual_orchestrator.decision", [call.name for call in fake.calls])

    @unittest.skip(LEGACY_FALSE_PROTOCOL)
    def test_dual_false_decision_does_not_expose_expected_correction(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            fake = FakeModelClient(
                {
                    "false_judgment_agent.assess": json.dumps(
                        {
                            "decision": "false",
                            "rationale": "The memories identify the counterexample n = 0.",
                            "false_evidence": "clear_counterexample",
                            "correction_to_true": "add hypothesis n ≠ 1",
                        }
                    ),
                    "dual_orchestrator.decision": json.dumps(
                        {
                            "decision": "continue",
                            "rationale": "The proposed correction is not supported by the evidence.",
                            "false_evidence": "clear_counterexample",
                            "correction_to_true": "add hypothesis n ≠ 1",
                        }
                    ),
                }
            )
            runtime = DualOrchestratorRuntime(
                model_client=fake,
                prompts=PromptRegistry.defaults(),
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                truth_memory=JsonlTrialMemory(Path(raw_dir) / "truth.jsonl"),
                falsity_memory=JsonlTrialMemory(Path(raw_dir) / "falsity.jsonl"),
            )

            decision = runtime.decide(
                problem="Prove every natural number is greater than one.",
                formal_statement="theorem bad (n : Nat) : n > 1 := by",
                truth_memory=[],
                falsity_memory=[],
                expected_false_fix=["add hypothesis n ≠ 0"],
            )

        self.assertEqual(decision["decision"], "continue")
        self.assertIn("not supported", decision["rationale"])
        decision_prompt = next(
            call for call in fake.calls if call.name == "dual_orchestrator.decision"
        )
        self.assertNotIn("expected_correction", decision_prompt.inputs)

    @unittest.skip(LEGACY_FALSE_PROTOCOL)
    def test_dual_false_decision_requires_explicit_rationale(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            fake = FakeModelClient(
                {
                    "false_judgment_agent.assess": json.dumps(
                        {
                            "decision": "false",
                            "rationale": "",
                            "false_evidence": "validated_counterexample",
                            "correction_to_true": "add hypothesis h",
                        }
                    ),
                    "dual_orchestrator.decision": json.dumps(
                        {
                            "decision": "false",
                            "rationale": "",
                            "false_evidence": "validated_counterexample",
                            "correction_to_true": "add hypothesis h",
                        }
                    ),
                }
            )
            runtime = DualOrchestratorRuntime(
                model_client=fake,
                prompts=PromptRegistry.defaults(),
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                truth_memory=JsonlTrialMemory(Path(raw_dir) / "truth.jsonl"),
                falsity_memory=JsonlTrialMemory(Path(raw_dir) / "falsity.jsonl"),
            )

            decision = runtime.decide(
                problem="A hard problem.",
                formal_statement="theorem hard : False := by",
                truth_memory=[],
                falsity_memory=[],
                expected_false_fix=["add hypothesis h"],
            )

        self.assertEqual(decision["decision"], "continue")
        self.assertEqual(decision["false_evidence"], "validated_counterexample")
        self.assertIn("clearly explain", decision["rationale"])

    def test_dual_decision_node_never_solves_true(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            fake = FakeModelClient(
                {
                    "dual_orchestrator.truth_strategy": "Assume true and try proof.",
                    "dual_orchestrator.falsity_strategy": "Assume false and attack.",
                    "truth_nature_agent.initial": "Bad proof.",
                    "truth_lean_generator.generate": (
                        "theorem generated_bad : 1 = 2 := by\n  rfl"
                    ),
                    "truth_retry_planner.plan": "Try again.",
                    "falsity_nature_agent.initial": "Attack the statement.",
                    "false_judgment_agent.assess": json.dumps(
                        {
                            "decision": "true",
                            "rationale": "The theorem is mathematically true.",
                            "false_evidence": "none",
                        }
                    ),
                    "dual_orchestrator.decision": json.dumps(
                        {
                            "decision": "true",
                            "rationale": "The theorem appears true.",
                            "false_evidence": "none",
                        }
                    ),
                }
            )
            orchestrator = DualOrchestrator(
                model_client=fake,
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                truth_memory=JsonlTrialMemory(Path(raw_dir) / "truth.jsonl", lane="truth"),
                falsity_memory=JsonlTrialMemory(
                    Path(raw_dir) / "falsity.jsonl", lane="falsity"
                ),
                project_root=ROOT,
                max_trials=1,
                max_rounds=1,
            )

            result = orchestrator.run("Do not solve without verified Lean.")

        self.assertEqual(result["decision"], "continue")
        self.assertEqual(result["final_status"], "not_solved")
        self.assertNotEqual(result["final_status"], "solved")

    @unittest.skip(LEGACY_FALSE_PROTOCOL)
    def test_dual_decision_receives_cumulative_memory_across_rounds(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            fake = FakeModelClient(
                {
                    "dual_orchestrator.truth_strategy": "Assume true and try a proof.",
                    "dual_orchestrator.falsity_strategy": "Assume false and attack.",
                    "truth_nature_agent.initial": "Attempt the proof directly.",
                    "truth_lean_generator.generate": (
                        "theorem generated_bad : 1 = 2 := by\n  rfl"
                    ),
                    "truth_retry_planner.plan": "Try a different proof.",
                    "falsity_nature_agent.initial": "Search for a counterexample.",
                    "false_judgment_agent.assess": json.dumps(
                        {
                            "decision": "continue",
                            "rationale": "No decisive evidence yet.",
                            "false_evidence": "none",
                        }
                    ),
                    "dual_orchestrator.decision": [
                        json.dumps(
                            {
                                "decision": "continue",
                                "rationale": "Run another round.",
                                "false_evidence": "none",
                            }
                        ),
                        json.dumps(
                            {
                                "decision": "continue",
                                "rationale": "Still inconclusive.",
                                "false_evidence": "none",
                            }
                        ),
                    ],
                }
            )
            orchestrator = DualOrchestrator(
                model_client=fake,
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                truth_memory=JsonlTrialMemory(Path(raw_dir) / "truth.jsonl", lane="truth"),
                falsity_memory=JsonlTrialMemory(
                    Path(raw_dir) / "falsity.jsonl", lane="falsity"
                ),
                project_root=ROOT,
                max_trials=1,
                max_rounds=2,
            )

            result = orchestrator.run("Keep all prior round evidence.")

        decision_prompts = [
            call for call in fake.calls if call.name == "dual_orchestrator.decision"
        ]
        self.assertEqual(result["rounds"], 2)
        self.assertEqual(len(decision_prompts), 2)
        first_truth = json.loads(decision_prompts[0].inputs["truth_memory"])
        first_falsity = json.loads(decision_prompts[0].inputs["falsity_memory"])
        second_truth = json.loads(decision_prompts[1].inputs["truth_memory"])
        second_falsity = json.loads(decision_prompts[1].inputs["falsity_memory"])
        self.assertEqual(len(first_truth["trials"]), 1)
        self.assertEqual(len(first_falsity), 1)
        self.assertEqual(len(second_truth["trials"]), 2)
        self.assertEqual(len(second_falsity), 2)

    @unittest.skip(LEGACY_FALSE_PROTOCOL)
    def test_dual_decision_model_error_continues_conservatively(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            fake = FakeModelClient(
                {
                    "false_judgment_agent.assess": json.dumps(
                        {
                            "decision": "false",
                            "rationale": "Potential false.",
                            "false_evidence": "clear_counterexample",
                            "correction_to_true": "fix target",
                        }
                    ),
                    "dual_orchestrator.decision": [
                        ModelClientError("decision timed out")
                    ],
                }
            )
            runtime = DualOrchestratorRuntime(
                model_client=fake,
                prompts=PromptRegistry.defaults(),
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                truth_memory=JsonlTrialMemory(Path(raw_dir) / "truth.jsonl"),
                falsity_memory=JsonlTrialMemory(Path(raw_dir) / "falsity.jsonl"),
            )

            decision = runtime.decide(
                problem="A hard problem.",
                formal_statement="theorem hard : False := by",
                truth_memory=[],
                falsity_memory=[],
                expected_false_fix=["fix target"],
            )

        self.assertEqual(decision["decision"], "continue")
        self.assertEqual(decision["false_evidence"], "none")
        self.assertIn("Decision model failed", decision["rationale"])

    def test_dual_final_status_maps_to_three_external_states(self) -> None:
        self.assertEqual(
            DualOrchestratorRuntime._final_status({"decision": "true"}),
            "solved",
        )
        self.assertEqual(
            DualOrchestratorRuntime._final_status({"decision": "false"}),
            "false",
        )
        self.assertEqual(
            DualOrchestratorRuntime._final_status({"decision": "continue"}),
            "not_solved",
        )

    def test_dual_failure_reason_distinguishes_generation_timeout(self) -> None:
        reason = DualOrchestratorRuntime._failure_reason(
            {
                "success": False,
                "timed_out": True,
                "has_prohibited_placeholder": False,
                "lean_error_log": (
                    "truth Lean generation model failed: codex exec timed out "
                    "after 600 seconds for truth_lean_generator.generate"
                ),
            },
            {},
        )

        self.assertEqual(
            reason,
            "Lean generation model timed out before producing Lean code.",
        )

    @unittest.skip(LEGACY_FALSE_PROTOCOL)
    def test_dual_runs_three_truth_trials_and_one_falsity_opinion_per_round(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            truth_path = Path(raw_dir) / "truth.jsonl"
            falsity_path = Path(raw_dir) / "falsity.jsonl"
            fake = FakeModelClient(
                {
                    "dual_orchestrator.truth_strategy": "Try direct proof.",
                    "dual_orchestrator.falsity_strategy": "Try to falsify once.",
                    "truth_nature_agent.initial": "Bad proof.",
                    "truth_nature_agent.retry": "Still bad proof.",
                    "truth_lean_generator.generate": "theorem generated_bad : 1 = 2 := by\n  rfl",
                    "truth_retry_planner.plan": "Fix the failed proof.",
                    "falsity_nature_agent.initial": "No clear counterexample.",
                    "dual_orchestrator.decision": json.dumps(
                        {
                            "decision": "continue",
                            "rationale": "No proof and no validated counterexample.",
                            "false_evidence": "none",
                        }
                    ),
                }
            )
            orchestrator = DualOrchestrator(
                model_client=fake,
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                truth_memory=JsonlTrialMemory(truth_path, lane="truth"),
                falsity_memory=JsonlTrialMemory(falsity_path, lane="falsity"),
                project_root=ROOT,
                max_trials=3,
                max_rounds=1,
            )

            result = orchestrator.run("Exercise one dual round.")

            self.assertEqual(result["trials"], 3)
            self.assertEqual(result["dual_truth_trials"], 3)
            self.assertEqual(result["dual_falsity_opinions"], 1)
            self.assertEqual(result["dual_falsity_trials"], 1)
            self.assertEqual(len(result["trial_memory"]), 4)
            self.assertEqual(
                [record["lane"] for record in result["trial_memory"]],
                ["truth", "truth", "truth", "falsity"],
            )
            call_names = [call.name for call in fake.calls]
            self.assertEqual(call_names.count("falsity_nature_agent.initial"), 1)
            self.assertNotIn("falsity_nature_agent.retry", call_names)
            self.assertNotIn("falsity_lean_generator.generate", call_names)
            self.assertNotIn("falsity_retry_planner.plan", call_names)
            self.assertEqual(len(truth_path.read_text(encoding="utf-8").splitlines()), 3)
            self.assertEqual(len(falsity_path.read_text(encoding="utf-8").splitlines()), 1)

    def test_dual_truth_and_falsity_strategies_are_created_in_parallel(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            fake = DelayedStrategyModelClient(delay_seconds=0.2)
            runtime = DualOrchestratorRuntime(
                model_client=fake,
                prompts=PromptRegistry.defaults(),
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                truth_memory=JsonlTrialMemory(Path(raw_dir) / "truth.jsonl"),
                falsity_memory=JsonlTrialMemory(Path(raw_dir) / "falsity.jsonl"),
            )

            truth_strategy, falsity_strategy = runtime.run_strategy_pair(
                problem="A problem.",
                formal_statement="theorem example : True := by",
                lean_header="",
                round_summaries=[],
                strategy_round=1,
            )

        self.assertEqual(truth_strategy, "dual_orchestrator.truth_strategy response")
        self.assertEqual(falsity_strategy, "dual_orchestrator.falsity_strategy response")
        truth_start, truth_end = fake.intervals["dual_orchestrator.truth_strategy"]
        falsity_start, falsity_end = fake.intervals["dual_orchestrator.falsity_strategy"]
        self.assertLess(max(truth_start, falsity_start), min(truth_end, falsity_end))
        call_names = [call.name for call in fake.calls]
        self.assertCountEqual(
            call_names,
            ["dual_orchestrator.truth_strategy", "dual_orchestrator.falsity_strategy"],
        )

    def test_dual_truth_success_records_falsifier_then_skips_decision(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            fake = FakeModelClient(
                {
                    "dual_orchestrator.truth_strategy": "Assume true and prove directly.",
                    "dual_orchestrator.falsity_strategy": "Assume false and attack.",
                    "truth_nature_agent.initial": "Both sides are definitionally equal.",
                    "truth_lean_generator.generate": (
                        "theorem generated_example : 1 = 1 := by\n  rfl"
                    ),
                    "falsity_nature_agent.initial": "Try to find a counterexample anyway.",
                }
            )
            orchestrator = DualOrchestrator(
                model_client=fake,
                verifier=LakeVerifier(ROOT, timeout_seconds=60),
                truth_memory=JsonlTrialMemory(Path(raw_dir) / "truth.jsonl", lane="truth"),
                falsity_memory=JsonlTrialMemory(
                    Path(raw_dir) / "falsity.jsonl", lane="falsity"
                ),
                project_root=ROOT,
                max_trials=1,
                max_rounds=3,
            )

            result = orchestrator.run(
                "Prove that 1 equals 1.",
                formal_statement="theorem generated_example : 1 = 1 := by",
            )

        self.assertEqual(result["decision"], "true")
        self.assertEqual(result["final_status"], "solved")
        self.assertEqual(result["trials"], 1)
        self.assertEqual(result["dual_truth_trials"], 1)
        self.assertEqual(result["dual_falsity_opinions"], 1)
        self.assertEqual(result["dual_falsity_trials"], 1)
        self.assertEqual(
            [record["lane"] for record in result["trial_memory"]],
            ["truth", "falsity"],
        )
        self.assertIn("falsity_nature_agent.initial", [call.name for call in fake.calls])
        self.assertNotIn("falsity_lean_generator.generate", [call.name for call in fake.calls])
        self.assertNotIn("dual_orchestrator.decision", [call.name for call in fake.calls])
        self.assertNotIn("llm_judge.proofnet_equivalence", [call.name for call in fake.calls])


if __name__ == "__main__":
    unittest.main()
