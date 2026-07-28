# Security

Do not commit API keys, OAuth tokens, `.env`, LangSmith credentials, or raw
provider responses that contain secrets.

Use `.env.example` as the template and keep real values in `.env`, which is
ignored by Git.

Codex OAuth credentials are managed by the Codex CLI outside this repository.
Do not copy Codex authentication files into the project directory.

Install the local pre-commit hook:

```bash
scripts/install_git_hooks.sh
```

Run the scanner manually at any time:

```bash
python scripts/check_secrets.py
python scripts/check_secrets.py --staged
```

If a credential has previously been pasted into a log, issue, chat, or commit,
revoke it and create a new credential before publishing this repository.
