# Single and Dual LLM–Lean Architectures

This repository is the reproducibility package for an experiment comparing two
LLM–Lean architectures on a mixture of true and false mathematical statements.

- **Single** uses one formalization path without assuming that the statement is
  true or false.
- **Dual** runs a truth-oriented formalization path and a falsity-oriented
  natural-language path, then combines their evidence conservatively.

The public evaluation subset contains 100 problems: 50 true statements and 50
false statements. The false statements are balanced across five mutation types.

## Reported results

| Architecture | True Solved | True Not Solved | Mean Rounds to Solve | False Detected | False Not Solved |
|---|---:|---:|---:|---:|---:|
| Single | 35 | 15 | 1.14 | 0 | 50 |
| Dual | 38 | 12 | 1.16 | 24 | 26 |

Neither architecture classified a true statement as false in the reported run.
The raw per-problem result files are under [`results/paper`](results/paper).

## Repository layout

```text
.
├── configs/                 # Exact model and budget settings
├── data/set_01 ... set_05/  # 20 problems and evaluator keys per set
├── docs/                    # Architecture figure
├── results/paper/           # Sanitized reported result JSONL files
├── scripts/                 # Setup, execution, and aggregation commands
├── src/                     # Single and Dual implementation
└── tests/                   # Unit and integration tests
```

## Requirements

- macOS or Linux
- Python 3.11 or newer
- Git
- Elan and Lean/Lake
- Codex CLI with an authenticated OAuth session
- An OpenRouter API key

The reported environment used:

- Python 3.13.3
- Lean 4.27.0 through the pinned miniF2F checkout
- Codex CLI 0.139.0
- miniF2F commit `f0a20e14c1eeccd859d51bb4c2b3ee487889c303`

The repository root also contains a Lean 4.32 development toolchain used by
auxiliary local tests. Paper evaluation runs inside the pinned miniF2F project,
whose own `lean-toolchain` selects Lean 4.27.0.

## Installation

```bash
python3 -m venv .venv
source .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -e ".[test]"
```

Prepare the pinned miniF2F checkout:

```bash
scripts/setup_minif2f.sh
```

Authenticate the Codex CLI, then prepare the OpenRouter environment:

```bash
codex login
cp .env.example .env
```

Set `OPENROUTER_API_KEY` in `.env`. Never commit `.env`.

Install the repository's pre-commit safety checks:

```bash
scripts/install_git_hooks.sh
```

The hook rejects common API-key formats, non-empty secret assignments,
credential files, and machine-specific home-directory paths.

## Reproduce one set

The command requires `--run` because it makes paid model calls:

```bash
scripts/run_paper_experiment.sh --set 01 --mode both --run
```

Valid sets are `01` through `05`. Valid modes are `single`, `dual`, and `both`.
New output is written under `.runs/paper/`.

To run all five sets:

```bash
for set_number in 01 02 03 04 05; do
  scripts/run_paper_experiment.sh --set "$set_number" --mode both --run
done
```

Model routing is strict. No unconfigured model fallback is allowed:

- Natural, False Reasoner, and Repair/Retry agents:
  `openai/gpt-5.4-nano` through OpenRouter
- Orchestrator and Lean Generator: `gpt-5.4` through Codex CLI OAuth

The historical CLI option is named `--nature-model`; it routes the Natural
Agent and is retained to avoid changing the evaluated implementation.

## Recreate the result table

```bash
python scripts/validate_release.py
python scripts/summarize_results.py
```

Use new run outputs instead:

```bash
python scripts/summarize_results.py \
  --results-root .runs/paper \
  --data-root data
```

## Important reproducibility note

The reported Dual run supplied the Falsifier output as `counter_reasoning`
inside the third truth-memory record. The current improved implementation can
instead expose `truth_memory` and `falsifier_memory` as separate schema fields.
The paper reproduction script explicitly selects the historical
`paper_merged` layout. See [REPRODUCIBILITY.md](REPRODUCIBILITY.md) before
interpreting or extending the results.

LLM API outputs are non-deterministic and provider-side model aliases can
change. This repository reproduces the evaluated pipeline, prompts, data,
budgets, routing, and evaluator, but it cannot guarantee byte-identical model
responses.

## Tests

```bash
python scripts/check_secrets.py
LANGSMITH_TRACING=false python -m pytest -q
```

## Data and evaluation keys

The `mixed20.jsonl` files are model inputs. The `labels.jsonl` files contain
gold labels and hidden mutation/repair information used only by the final
conservative checker. See [DATASET.md](DATASET.md).

## License and citation

A source-code license and final citation metadata must be selected by the
authors before making the GitHub repository public. The miniF2F source should
be cited and used under its upstream terms.
