from __future__ import annotations

import os
from pathlib import Path
import sys
import time
import types
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from single_orchestrator.model import (
    CodexCliModelClient,
    CodexSdkModelClient,
    ModelClientError,
    OpenAICompatibleModelClient,
    make_default_model_client,
)
from single_orchestrator.prompts import BuiltPrompt


class ModelClientTest(unittest.TestCase):
    def test_openai_compatible_client_passes_configured_max_tokens(self) -> None:
        original_module = sys.modules.get("openai")
        old_key = os.environ.get("OPENAI_API_KEY")
        old_max_tokens = os.environ.get("DUAL_ARC_MAX_OUTPUT_TOKENS")
        captured: dict[str, object] = {}

        class FakeCompletions:
            def create(self, **kwargs):
                captured.update(kwargs)
                message = types.SimpleNamespace(content="ok")
                return types.SimpleNamespace(choices=[types.SimpleNamespace(message=message)])

        class FakeOpenAI:
            def __init__(self, **kwargs):
                self.chat = types.SimpleNamespace(completions=FakeCompletions())

        sys.modules["openai"] = types.SimpleNamespace(OpenAI=FakeOpenAI)
        os.environ["OPENAI_API_KEY"] = "test-key"
        os.environ["DUAL_ARC_MAX_OUTPUT_TOKENS"] = "60000"
        try:
            client = OpenAICompatibleModelClient(model="gpt-test", timeout_seconds=0)
            response = client.complete(
                BuiltPrompt(name="test", version="test", inputs={}, text="Return ok.")
            )
        finally:
            if original_module is None:
                sys.modules.pop("openai", None)
            else:
                sys.modules["openai"] = original_module
            if old_key is None:
                os.environ.pop("OPENAI_API_KEY", None)
            else:
                os.environ["OPENAI_API_KEY"] = old_key
            if old_max_tokens is None:
                os.environ.pop("DUAL_ARC_MAX_OUTPUT_TOKENS", None)
            else:
                os.environ["DUAL_ARC_MAX_OUTPUT_TOKENS"] = old_max_tokens

        self.assertEqual(response, "ok")
        self.assertEqual(captured["max_tokens"], 60000)

    def test_default_model_client_can_force_cli(self) -> None:
        old_value = os.environ.get("DUAL_ARC_MODEL_CLIENT")
        os.environ["DUAL_ARC_MODEL_CLIENT"] = "cli"
        try:
            client = make_default_model_client(
                Path("/tmp"),
                model="gpt-test",
                timeout_seconds=1,
            )
        finally:
            if old_value is None:
                os.environ.pop("DUAL_ARC_MODEL_CLIENT", None)
            else:
                os.environ["DUAL_ARC_MODEL_CLIENT"] = old_value

        self.assertIsInstance(client, CodexCliModelClient)

    def test_codex_sdk_timeout_covers_thread_start(self) -> None:
        original = sys.modules.get("openai_codex")

        class SlowCodex:
            def __enter__(self):
                return self

            def __exit__(self, exc_type, exc, traceback):
                return False

            def thread_start(self, **kwargs):
                time.sleep(5)
                raise AssertionError("thread_start should have timed out")

        fake_module = types.SimpleNamespace(
            Codex=lambda: SlowCodex(),
            Sandbox=types.SimpleNamespace(read_only="read_only"),
        )
        sys.modules["openai_codex"] = fake_module
        try:
            client = CodexSdkModelClient(model="gpt-test", timeout_seconds=1)
            prompt = BuiltPrompt(
                name="orchestrator.strategy",
                version="test",
                inputs={},
                text="Return ok.",
            )

            with self.assertRaisesRegex(ModelClientError, "codex sdk timed out after 1 seconds"):
                client.complete(prompt)
        finally:
            if original is None:
                sys.modules.pop("openai_codex", None)
            else:
                sys.modules["openai_codex"] = original


if __name__ == "__main__":
    unittest.main()
