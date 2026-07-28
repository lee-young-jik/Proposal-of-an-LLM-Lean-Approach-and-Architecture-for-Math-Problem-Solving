from __future__ import annotations

from dataclasses import dataclass
from contextlib import contextmanager
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import threading
import time
from typing import Mapping, Protocol

from .prompts import BuiltPrompt

try:
    from dotenv import load_dotenv
except ImportError:
    load_dotenv = None
else:
    load_dotenv()


class ModelClient(Protocol):
    def complete(self, prompt: BuiltPrompt) -> str:
        """Return the model response for a whitelisted prompt."""


class ModelClientError(RuntimeError):
    pass


@dataclass
class PromptRoutingModelClient:
    default_client: ModelClient
    prompt_clients: Mapping[str, ModelClient]
    strict: bool = False

    def complete(self, prompt: BuiltPrompt) -> str:
        client = self.prompt_clients.get(prompt.name)
        if client is None:
            if self.strict:
                raise ModelClientError(
                    f"No model route configured for prompt {prompt.name!r}."
                )
            client = self.default_client
        return client.complete(prompt)


@dataclass
class CodexCliModelClient:
    cwd: Path
    model: str | None = None
    timeout_seconds: int = 300

    def complete(self, prompt: BuiltPrompt) -> str:
        with tempfile.NamedTemporaryFile("r", encoding="utf-8", delete=True) as output_file:
            return self._complete_with_output_file(prompt, Path(output_file.name))

    def _complete_with_output_file(self, prompt: BuiltPrompt, output_path: Path) -> str:
        command = [
            "codex",
            "exec",
            "--skip-git-repo-check",
            "--ignore-user-config",
            "--sandbox",
            "read-only",
            "--ephemeral",
            "--output-last-message",
            str(output_path),
        ]
        if self.model:
            command.extend(["--model", self.model])
        command.append(prompt.text)

        try:
            completed = self._run_codex(command, prompt.name)
        except TimeoutError as exc:
            raise ModelClientError(
                f"codex exec timed out after {self.timeout_seconds} seconds "
                f"for {prompt.name}"
            ) from exc
        if completed.returncode != 0:
            detail = self._compact_codex_error(completed.stderr, completed.stdout)
            raise ModelClientError(f"codex exec failed for {prompt.name}: {detail}")

        final_message = output_path.read_text(encoding="utf-8").strip()
        if final_message:
            return final_message
        return completed.stdout.strip()

    def _run_codex(self, command: list[str], prompt_name: str) -> subprocess.CompletedProcess[str]:
        with tempfile.NamedTemporaryFile("w+", encoding="utf-8") as stdout_file:
            with tempfile.NamedTemporaryFile("w+", encoding="utf-8") as stderr_file:
                process = subprocess.Popen(
                    command,
                    cwd=self.cwd,
                    text=True,
                    stdin=subprocess.DEVNULL,
                    stdout=stdout_file,
                    stderr=stderr_file,
                    start_new_session=True,
                )
                deadline = (
                    time.monotonic() + self.timeout_seconds
                    if self.timeout_seconds > 0
                    else None
                )
                while process.poll() is None:
                    if deadline is not None and time.monotonic() >= deadline:
                        self._terminate_process_group(process)
                        raise TimeoutError(
                            f"codex exec exceeded {self.timeout_seconds} seconds "
                            f"for {prompt_name}"
                        )
                    time.sleep(0.5)
                stdout_file.seek(0)
                stderr_file.seek(0)
                return subprocess.CompletedProcess(
                    command,
                    process.returncode,
                    stdout=stdout_file.read(),
                    stderr=stderr_file.read(),
                )

    @staticmethod
    def _terminate_process_group(process: subprocess.Popen[str]) -> None:
        try:
            os.killpg(process.pid, signal.SIGTERM)
            process.wait(timeout=5)
        except Exception:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except Exception:
                process.kill()

    @staticmethod
    def _compact_codex_error(stderr: str, stdout: str, max_lines: int = 12) -> str:
        raw = "\n".join(part for part in (stderr.strip(), stdout.strip()) if part)
        if not raw:
            return "Codex CLI exited with a non-zero status and no output."

        kept: list[str] = []
        for line in raw.splitlines():
            stripped = line.strip()
            if not stripped:
                continue
            if stripped.startswith("ERROR:"):
                kept.append(stripped)
                continue
            if "ran out of room in the model's context window" in stripped:
                kept.append(stripped)
                continue
            if "timed out" in stripped.lower():
                kept.append(stripped)
                continue
            if "usage limit" in stripped.lower():
                kept.append(stripped)
                continue
            if "error sending request" in stripped:
                kept.append(stripped)
                continue
            if "stream disconnected" in stripped:
                kept.append(stripped)
                continue
            if stripped.startswith("codex") and not kept:
                kept.append(stripped)

        if not kept:
            kept = [line.strip() for line in raw.splitlines() if line.strip()][:max_lines]

        deduped: list[str] = []
        for line in kept:
            if line not in deduped:
                deduped.append(line)
        return "\n".join(deduped[:max_lines])


@dataclass
class CodexSdkModelClient:
    model: str | None = None
    timeout_seconds: int = 300

    def complete(self, prompt: BuiltPrompt) -> str:
        try:
            from openai_codex import Codex, Sandbox
        except ImportError as exc:
            raise ModelClientError(
                "openai-codex is not installed. Install the codex-sdk optional dependency "
                "or use CodexCliModelClient."
            ) from exc

        try:
            with _wall_clock_timeout(self.timeout_seconds):
                with Codex() as codex:
                    kwargs = {"sandbox": Sandbox.read_only}
                    if self.model:
                        kwargs["model"] = self.model
                    thread = codex.thread_start(**kwargs)
                    result = thread.run(prompt.text)
        except TimeoutError as exc:
            raise ModelClientError(
                f"codex sdk timed out after {self.timeout_seconds} seconds "
                f"for {prompt.name}"
            ) from exc
        return result.final_response.strip()


@dataclass
class OpenAICompatibleModelClient:
    model: str
    timeout_seconds: int = 300
    base_url: str | None = None
    api_key_env: str = "OPENAI_API_KEY"

    def complete(self, prompt: BuiltPrompt) -> str:
        try:
            from openai import OpenAI
        except ImportError as exc:
            raise ModelClientError(
                "openai is not installed. Install the OpenAI Python package "
                "to use OpenRouter/OpenAI-compatible models."
            ) from exc

        api_key = os.getenv(self.api_key_env)
        if not api_key:
            raise ModelClientError(f"{self.api_key_env} is not set.")
        api_key = _ascii_header_value(api_key).strip()

        try:
            request_timeout = self.timeout_seconds if self.timeout_seconds > 0 else None
            max_tokens_raw = os.getenv("DUAL_ARC_MAX_OUTPUT_TOKENS", "").strip()
            completion_options: dict[str, int] = {}
            if max_tokens_raw:
                completion_options["max_tokens"] = int(max_tokens_raw)
            client = OpenAI(
                api_key=api_key,
                base_url=self.base_url or os.getenv(
                    "OPENAI_BASE_URL", "https://openrouter.ai/api/v1"
                ),
                timeout=request_timeout,
            )
            with _wall_clock_timeout(self.timeout_seconds):
                response = client.chat.completions.create(
                    model=self.model,
                    messages=[{"role": "user", "content": prompt.text}],
                    extra_headers=self._extra_headers(),
                    **completion_options,
                )
        except Exception as exc:
            raise ModelClientError(
                f"OpenAI-compatible model call failed for {prompt.name}: {exc}"
            ) from exc

        message = response.choices[0].message.content if response.choices else ""
        if isinstance(message, list):
            return "\n".join(
                part.get("text", "") if isinstance(part, dict) else str(part)
                for part in message
            ).strip()
        return (message or "").strip()

    @staticmethod
    def _extra_headers() -> dict[str, str]:
        headers: dict[str, str] = {}
        referer = os.getenv("OPENROUTER_HTTP_REFERER")
        title = os.getenv("OPENROUTER_APP_TITLE")
        if referer:
            headers["HTTP-Referer"] = _ascii_header_value(referer)
        if title:
            headers["X-Title"] = _ascii_header_value(title)
        return headers


def _ascii_header_value(value: str) -> str:
    return value.encode("ascii", errors="ignore").decode("ascii")


@contextmanager
def _wall_clock_timeout(timeout_seconds: int):
    if timeout_seconds <= 0:
        yield
        return
    if threading.current_thread() is not threading.main_thread():
        yield
        return

    def raise_timeout(signum, frame):
        raise TimeoutError(f"model call exceeded {timeout_seconds} seconds")

    previous_handler = signal.getsignal(signal.SIGALRM)
    signal.signal(signal.SIGALRM, raise_timeout)
    signal.setitimer(signal.ITIMER_REAL, timeout_seconds)
    try:
        yield
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous_handler)


def make_default_model_client(
    cwd: Path,
    model: str | None = None,
    timeout_seconds: int = 300,
) -> ModelClient:
    preferred_client = os.getenv("DUAL_ARC_MODEL_CLIENT", "").strip().lower()
    compatible_config = _openai_compatible_config(model)
    if compatible_config is not None:
        compatible_model, base_url, api_key_env = compatible_config
        return OpenAICompatibleModelClient(
            model=compatible_model,
            timeout_seconds=timeout_seconds,
            base_url=base_url,
            api_key_env=api_key_env,
        )
    if preferred_client == "cli":
        return CodexCliModelClient(
            cwd=cwd,
            model=model,
            timeout_seconds=timeout_seconds,
        )
    if preferred_client and preferred_client != "sdk":
        raise ModelClientError(
            "DUAL_ARC_MODEL_CLIENT must be unset, 'sdk', or 'cli'."
        )
    try:
        import openai_codex  # noqa: F401
    except ImportError:
        return CodexCliModelClient(
            cwd=cwd,
            model=model,
            timeout_seconds=timeout_seconds,
        )
    return CodexSdkModelClient(model=model, timeout_seconds=timeout_seconds)


def make_prompt_routing_model_client(
    cwd: Path,
    *,
    default_model: str | None = None,
    timeout_seconds: int = 300,
    prompt_models: Mapping[str, str | None] | None = None,
    strict: bool = False,
) -> ModelClient:
    default_client = make_default_model_client(
        cwd,
        model=default_model,
        timeout_seconds=timeout_seconds,
    )
    prompt_clients: dict[str, ModelClient] = {}
    for prompt_name, model in (prompt_models or {}).items():
        if not model:
            continue
        if model == default_model:
            prompt_clients[prompt_name] = default_client
            continue
        prompt_clients[prompt_name] = make_default_model_client(
            cwd,
            model=model,
            timeout_seconds=timeout_seconds,
        )
    return PromptRoutingModelClient(
        default_client=default_client,
        prompt_clients=prompt_clients,
        strict=strict,
    )


def _uses_openai_compatible_api(model: str | None) -> bool:
    return _openai_compatible_config(model) is not None


def _openai_compatible_config(model: str | None) -> tuple[str, str, str] | None:
    if not model:
        return None
    if model.startswith("openai:"):
        return (
            model.removeprefix("openai:"),
            "https://api.openai.com/v1",
            "OPENAI_API_KEY",
        )
    if model.startswith("openrouter:"):
        return (
            model.removeprefix("openrouter:"),
            os.getenv("OPENROUTER_BASE_URL", "https://openrouter.ai/api/v1"),
            "OPENROUTER_API_KEY",
        )
    if "/" in model:
        return (
            model,
            os.getenv("OPENROUTER_BASE_URL", "https://openrouter.ai/api/v1"),
            "OPENROUTER_API_KEY",
        )
    return None
