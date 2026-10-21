# Full-memory Single / Dual: observed pass@1–3

Completed: **2026-10-21 04:43 KST** (2026-10-20 19:43 UTC), including result export.
This directory contains **864 scored executions**: 144 fixed problems × 2 architectures × 3 repetitions.
Repetition 1 reuses 288 historical full-memory executions; repetitions 2–3 add 576 fresh executions.
All planned repetitions were executed even when an earlier repetition solved the problem.

**Dataset limitation:** the 144 IDs are an outcome-selected development subset of the full 150
(original 121 + 23 retained Judson problems). Six Judson problems were excluded after first-run
results were inspected. No further ID selection was performed for repetitions 2–3.
These results do not establish performance on an independent, unbiased final test set.
See [selection disclosure](../../data/book144_posthoc_v1/README.md).

## Overall cumulative results

Here, observed prefix `pass@k` means that at least one of logical executions 1…k produced a
correct Lean-verified answer. This is a measured union over these specific executions, not
the unbiased combinatorial pass@k estimator. A repetition is a complete pipeline run,
not one round, one model call, or one Lean check. Memory starts empty in each repetition
and includes prior rounds only within that execution.

| Prefix | Single | Dual | Dual − Single |
|---|---:|---:|---:|
| pass@1 | 86/144 · 59.7% | 90/144 · 62.5% | +4 problems |
| pass@2 | 98/144 · 68.1% | 100/144 · 69.4% | +2 problems |
| pass@3 | 103/144 · 71.5% | 102/144 · 70.8% | −1 problem |

At pass@3, both solve 94 problems, Single alone solves 9, Dual alone solves 8, and neither
solves 33. The paired exact two-sided McNemar p-value is 1.0. The one-problem difference
does not establish superiority of either architecture. Dual's initial advantage narrows
as complete runs are repeated; a widening advantage on long reference proofs was not observed.

Each repetition evaluated on its own (not cumulative):

| Repetition | Single | Dual |
|---|---:|---:|
| 1 | 86/144 | 90/144 |
| 2 | 85/144 | 88/144 |
| 3 | 86/144 | 89/144 |

The architectures solve partly different problems. Thus Dual can solve more problems in
each individual repetition while Single has a slightly larger union across three repetitions.
See [paired_problem_results.csv](paired_problem_results.csv) for all per-problem outcomes.

## Reference proof length: selected 144

These are fixed groups based on the **dataset reference Lean proof body**, after stripping
comments and counting non-whitespace Unicode characters. Generated answer length does not
determine the group. Sort by `(reference_characters, id)` and divide into equal rank groups.
Short: 13–110 characters; medium: 111–513; long: 535–3188; 48 problems each.

| Prefix | Group | Single | Dual |
|---|---|---:|---:|
| pass@1 | Short · 48 | 46 · 95.8% | 46 · 95.8% |
| | Medium · 48 | 28 · 58.3% | 29 · 60.4% |
| | Long · 48 | 12 · 25.0% | 15 · 31.3% |
| pass@2 | Short · 48 | 46 · 95.8% | 47 · 97.9% |
| | Medium · 48 | 34 · 70.8% | 35 · 72.9% |
| | Long · 48 | 18 · 37.5% | 18 · 37.5% |
| pass@3 | Short · 48 | 46 · 95.8% | 47 · 97.9% |
| | Medium · 48 | 37 · 77.1% | 36 · 75.0% |
| | Long · 48 | 20 · 41.7% | 19 · 39.6% |

## Original 121 versus added 23

| Cohort | Prefix | Single | Dual |
|---|---|---:|---:|
| Original 121 | pass@1 | 78 · 64.5% | 80 · 66.1% |
| | pass@2 | 89 · 73.6% | 89 · 73.6% |
| | pass@3 | 92 · 76.0% | 91 · 75.2% |
| Added 23 | pass@1 | 8 · 34.8% | 10 · 43.5% |
| | pass@2 | 9 · 39.1% | 11 · 47.8% |
| | pass@3 | 11 · 47.8% | 11 · 47.8% |

The added 23 do not cause the final Single advantage: they tie at pass@3.
The one-problem difference occurs within the original 121.

The original 121 have their **own historical reference tertiles**, 40/41/40.
These are not the 144-problem cutoffs applied to a smaller subset:

| Prefix | Original121 group | Single | Dual |
|---|---|---:|---:|
| pass@1 | Short · 40 | 39 · 97.5% | 38 · 95.0% |
| | Medium · 41 | 28 · 68.3% | 29 · 70.7% |
| | Long · 40 | 11 · 27.5% | 13 · 32.5% |
| pass@2 | Short · 40 | 39 · 97.5% | 39 · 97.5% |
| | Medium · 41 | 33 · 80.5% | 35 · 85.4% |
| | Long · 40 | 17 · 42.5% | 15 · 37.5% |
| pass@3 | Short · 40 | 39 · 97.5% | 39 · 97.5% |
| | Medium · 41 | 35 · 85.4% | 36 · 87.8% |
| | Long · 40 | 18 · 45.0% | 16 · 40.0% |

At pass@3 on original121: both 84, Single only 8, Dual only 7, neither 22.
All cohort/group counts are in [cohort_pass_at_k.csv](cohort_pass_at_k.csv).

## Cost, tokens, and Lean verification

Totals include all three scored executions, including executions after an earlier success.
Prices are the actual provider-reported USD amounts in the saved responses, not a current
price-list estimate. Provider usage/cost fields are retained at call level.

| Metric | Single | Dual |
|---|---:|---:|
| Scored executions | 432 | 432 |
| Reported cost | $4.036227625 | $7.065118120 |
| Input tokens | 42,552,454 | 80,978,030 |
| Output tokens | 6,988,819 | 11,545,640 |
| Actual Lean checks | 2,257 | 4,089 |

Separate provider-reported infrastructure overhead (quarantined attempts + health probes)
is **$0.5245868325**. Missing provider usage is not evidence of zero billing. Details are
in `quarantined_usage/`, `service_usage/`, and `summary.json`.
Dual permits up to 18 Lean attempts per execution versus Single's 9; equal repetitions
are not equal verification/token/cost budgets. Wall-clock comparisons are also affected
by concurrency changes, provider latency, and serialized Lean builds.

## Architecture and protocol

- Orchestrator: `openai/gpt-6-luna-pro`; Natural, Generator, Repair: `openai/gpt-6-luna`.
- OpenRouter route pinned to `openai/flex`, with no model/provider fallback.
- 3 rounds × 3 Lean trials per lane. Single chooses a goal each round; Dual has fixed prove/disprove lanes.
- Orchestrator receives previous-round strategies, independent natural arguments, and Lean code;
  compiler errors and Repair guidance are not added to its memory.
- Natural reasons independently. Repair emits one retry-guidance output for within-round generation.
- No memory is carried between independent repetitions. No no-memory repetitions 2–3 were run.
- Recovery experiments and output-budget interventions were disabled.
- Scheduling increased from four to six workers, without canceling in-flight model calls.
- The original pass@5 plan was reduced to pass@3 before any repetition 4/5 started.
  Historical script/run-directory names containing `pass5` remain in audit metadata for traceability.

The protocol is in [FINAL_PIPELINE.md](../../docs/FINAL_PIPELINE.md); `baseline.env`,
`plan.json`, input data, evaluator labels, source hashes, and offline checks are included here.
Each raw run includes its evaluated source snapshot. Evaluator labels were not model inputs.

## Infrastructure failures and completeness

24 affected executions were quarantined and rerun with fresh run IDs and the same model,
prompt, and attempt budgets. Error attempts were not scored as mathematical failures.
Original error logs remain available. `infra_retry_integrity.json` verifies replacement
identity and ordering for all 24; `all_clean=true`, with zero held canonical runs.
The canonical usage audit reconciles **18,231 requests and 18,231 responses** to saved
per-run totals. `publication_verification.json` verifies 864 unique run keys and 144 IDs.

## Combine with earlier results

Use `(id, mode, repetition, memory_condition)` as the repeated-run key. Use `id` to join
dataset reference data. Fields named `correct` are evaluator outcomes; raw Lean acceptance
alone should not be used to replace the conservative evaluator decision.

- `runs.jsonl`: all 864 full-memory scored rows; `runs_rep1/2/3.jsonl`: repetition subsets.
- `scored_runs_for_join.jsonl`: the same outcomes with explicit `memory_condition=full`,
  integer repetition and cohort/group fields for joining; historical rows in `runs.jsonl`
  may omit `memory_condition` and inherit it from the file's full-memory condition.
- `paired_problem_results.csv`: one row per ID, all six execution outcomes and pass@1–3.
- `pass_at_k.csv`: full144/group curves; `cohort_pass_at_k.csv`: original121/add23/full144 curves.
- `usage/api_calls.csv`, `usage/raw_usage.jsonl`: call-level usage, model, role, round, and trial.
- `usage/by_repetition_agent.csv`, `by_problem_agent.csv`, `by_round_agent.csv`: usage summaries.
- `prior_memory_comparison150/runs_full.jsonl` and `runs_none.jsonl`: earlier first-run full/none data,
  **not additional repetitions**. Deduplicate reused full-memory rows rather than counting them twice.
- Earlier first-run full/none: original121 Single 78/71, Dual 80/72; full150 Single 87/82,
  Dual 91/81; selected144 Single 86/77, Dual 90/77. These are separate memory comparisons,
  not pass@3 ablations. The full150 records preserve the six excluded cases.
- `selected144_reference_ratios.csv`: earlier first-success generated/reference code ratios.
  These are historical pass@1 ratios, not recomputed pass@3 ratios.

## Detailed logs and provenance

Large archives are attached to the [GitHub Release](https://github.com/lee-young-jik/Proposal-of-an-LLM-Lean-Approach-and-Architecture-for-Math-Problem-Solving/releases/tag/book144-full-memory-pass3-20261021):

- `book144_pass3_rep1_raw_logs_20261020.zip`: 288 historical canonical runs.
- `book144_pass3_rep2_raw_logs_20261020.zip`: 288 second-repetition canonical runs.
- `book144_pass3_rep3_raw_logs_20261020.zip`: 288 third-repetition canonical runs.
- `book144_pass3_supervision_20261020.zip`: scheduler, model-response monitoring, health probes,
  quarantined runs, and retry incidents.
- `book144_full_pass3_public_tables_20261021.zip`: this result directory in one download.

Raw canonical archives contain model request instructions/inputs, responses, node events,
strategies, natural reasoning, generated Lean, verifier errors, retry guidance, outcome,
manifest, and source snapshot. Existing audit metadata determines which fields were saved;
no claim is made about unlogged provider-internal information.

Public copies normalize private machine paths only. Local originals are untouched.
Embedded original hashes describe pre-normalization files; each archive has a separate
`PUBLICATION_MANIFEST.json` with original and public per-file hashes. Public archive hashes
and original archive hashes are in `publication_provenance.json`. `public_sha256.json`
checks the published repository files; `release_assets.json` links downloads and checksums.
Authentication keys and root `.env` files are not included; `baseline.env` is non-secret configuration.
