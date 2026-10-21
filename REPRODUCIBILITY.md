# Reproducibility: 137-problem analysis

## Task and evaluation

137 textbook problems, 62 Prove / 75 Disprove. Inputs contain statements and goals;
labels/reference proofs/selection metadata are evaluator-only. Pass@5 is the union
of successes over five complete executions. Each execution has fresh memory and
at most 3 strategy rounds with 3 Lean attempts per lane per round. Single has at
most 9 attempts, Dual 18; identical round limits are not equal compute budgets.

The dataset is outcome-selected, and two IDs have five-run replacements. Full
conditions and excluded IDs are in [dataset provenance](data/book137_posthoc_v1/README.md).
The final scores are exploratory. Numeric aggregation uses the published scored
rows; raw local replacement-run logs and generated outputs are not bundled.

## Exact configuration

[Runtime settings](configs/two_goal_experiment.env) and
[actual role prompts](src/single_orchestrator/goal_prompts.py) are the source of truth.

| Setting | Value |
|---|---|
| Orchestrator | `openai/gpt-6-luna-pro` |
| Natural / Generator / Repair | `openai/gpt-6-luna` |
| Provider | `openai/flex`, no silent fallback |
| Worker reasoning effort | `none` |
| Planner reasoning | Model alias default |
| Generated-output limit | 16,384 tokens; Repair 2,048 |
| Model-call timeout | 900 s |
| Repair timeout | 180 s |
| Lean verification timeout | 300 s |
| Lean | 4.27.0 |
| Mathlib | `a3a10db0e9d66acbebf76c5e6a135066525ac900` |
| miniF2F environment | `f0a20e14c1eeccd859d51bb4c2b3ee487889c303` |
| Tested Python | 3.13.3 |

The miniF2F checkout supplies the pinned Lean environment; it is not the evaluation
dataset. Temperature/top-p/model sampling seeds are not fixed by this config;
omitted request fields use provider defaults. The runner's order seed shuffles
jobs and is not an LLM sampling seed. Hosted model aliases and stochastic outputs
can change; new runs need not reproduce historical outcomes exactly.

## Checks and logs

`python scripts/validate_release.py` checks dataset hashes, label separation, counts,
reference-answer alignment, five executions per mode/problem and reported accuracy,
code-length and completion-round aggregates. It makes no paid API calls and does
not re-certify historical proofs or API usage. Reference answers contain complete
Lean code for optional verification in the pinned environment.

[Installation](docs/CURRENT_SETUP.md) · [Role flow](docs/FINAL_PIPELINE.md) ·
[Audit log format and new-run analysis](docs/experiment_logging.md)
