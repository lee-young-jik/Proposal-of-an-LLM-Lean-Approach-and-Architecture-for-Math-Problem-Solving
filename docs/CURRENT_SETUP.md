# Move the current Single/Dual system to another computer

This guide covers the retained original shared prompts and the two-goal runtime,
not the archived paper configuration. It supports macOS/Linux and Python 3.11+.
Keep the same Lean project pin and config when comparing results.

## Install

```bash
git clone https://github.com/lee-young-jik/Proposal-of-an-LLM-Lean-Approach-and-Architecture-for-Math-Problem-Solving.git
cd Proposal-of-an-LLM-Lean-Approach-and-Architecture-for-Math-Problem-Solving
python3 -m venv .venv
source .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -r requirements-tested.txt
python -m pip install -e .
```

`requirements-tested.txt` pins the four top-level packages from the tested local
environment; it is not a complete transitive dependency lock. The evaluation
environment used Python 3.13.3. Install Elan (the Lean toolchain manager) and
ensure `lake` is on PATH, then prepare the pinned Lean 4.27.0/Mathlib environment:

```bash
scripts/setup_minif2f.sh
```

The script clones miniF2F at
`f0a20e14c1eeccd859d51bb4c2b3ee487889c303` and runs `lake build`.
It deliberately refuses to overwrite an existing checkout. Existing users can
keep their already prepared `.datasets/miniF2F-lean4` directory.

## Credentials and configuration

```bash
cp .env.example .env
```

Fill `OPENROUTER_API_KEY` locally. The retained config is
`configs/two_goal_experiment.env`: Orchestrator `openai/gpt-6-luna-pro`, workers
`openai/gpt-6-luna`, worker reasoning `none`, pinned `openai/flex` provider with
no silent fallback. Availability depends on the provider/account; change a
route explicitly and report a new configuration if the pinned endpoint is
unavailable. This configuration does not need Codex CLI/OAuth.

LangSmith is optional: fill its key and set `LANGSMITH_TRACING=true` and
`LANGCHAIN_TRACING_V2=true` in `.env`; choose `LANGSMITH_PROJECT` as desired.
Never commit `.env`. Local `audit/` records are written even with tracing off.

## Check without paid model calls

```bash
python scripts/check_two_goal_search.py --offline-only
python scripts/check_goal_lane_isolation.py
python scripts/check_flex_model_setup.py
python scripts/check_repair_context.py
python scripts/check_secrets.py
```

## Plan, then run

The portable JSONL uses split `book121`. This example selects two familiar
development cases and runs Single and Dual once each: four complete executions.
The first command only saves a plan, with no model calls:

```bash
python scripts/run_logged_experiment.py \
  --jsonl data/book121_v1/problems.jsonl --split book121 \
  --ids linear_algebra_6A_24 calculus_23_3_7 \
  --project-root .datasets/miniF2F-lean4 \
  --config-env configs/two_goal_experiment.env \
  --repetitions 1 --memory-conditions full \
  --output-dir .runs/transfer_plan
```

To execute paid calls, repeat that command with a **new** output directory such
as `.runs/transfer_test` and append `--run`. Existing output directories are not
overwritten. Choose other IDs from `problems.jsonl` or the recorded balanced22
list as needed. The script defaults to five repetitions if omitted, so specify
`--repetitions 1` for one pass.

The runner passes each problem's Lean prelude through to both verifier CLIs.
Do not use `labels.jsonl` as `--jsonl`. It is only for offline grading:

```bash
python scripts/analyze_logged_experiment.py .runs/transfer_test \
  --labels data/book121_v1/labels.jsonl \
  --metadata data/book121_v1/problems.jsonl
```

## Retained behavior and evidence

- Three strategy rounds, three attempts per lane per round. Single can use nine
  attempts, Dual eighteen; the total compute budgets differ.
- Single chooses a direction per round and reads its own prior records. Dual
  keeps two fixed directions and reads both previous-round records.
- Planner history contains strategies, independent arguments and code; it
  excludes raw errors, error summaries and Repair guidance.
- Natural works independently of Planner strategy/history. Repair advises the
  Generator about Lean errors; it does not directly patch code or summarize
  errors into Planner memory.
- A worker output error consumes that lane's attempt rather than terminating
  the other lane. Infrastructure failures remain errors.
- Common Lean declaration/context support is enabled for both architectures.
  It does not add a separate theorem-search agent.
- Numbered-step strategy instructions were tested and rejected; the original
  common prompts were restored.

The balanced22 result was Single15/Dual16; the later two-case fresh comparison
was original Single0/Dual2 versus stepwise Single0/Dual0. These are exploratory
single-pass results, not guarantees for a new run. See
[balanced22 results](balanced22_results_20261017.txt) and
[stepwise comparison](stepwise_strategy_two_results_20261018.txt).

Run outputs and credentials are intentionally not uploaded. New evaluations
write their own `.runs/` audits; references to older local `.runs/` in analysis
reports identify historical evidence that is not bundled in this checkout.
