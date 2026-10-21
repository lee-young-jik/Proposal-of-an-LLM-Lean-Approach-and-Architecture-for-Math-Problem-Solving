# Orchestrator history ablation: full versus none

Completed experiment, published 2026-10-21. **One complete execution per problem, architecture,
and memory condition**: 150 problems × Single/Dual × full/none = **600 scored executions**.
The original 121 results are preserved; 29 new Judson problems add 116 executions.
This package publishes the no-history results, their full-memory comparators, detailed usage,
frozen sources, infrastructure incidents, and problem-level joins.

**No-memory pass@2 or pass@3 was run.** The separate
[full-memory pass@3 experiment](../book144_full_pass3_20261020/README.md) repeated only the
full condition. Do not compare its three-run union directly against this one-run none condition
as an estimate of memory benefit.

## What was removed

Only the Orchestrator's prior-round `trial_memory` input is emptied on every round.
It still receives the original problem and Lean goal(s), plus the unchanged role instructions.

- Single does not receive its own prior-round strategy, natural argument, or Lean code.
- Dual does not receive either lane's prior-round strategy, natural argument, or Lean code.
- Natural remains an independent reasoner in both conditions.
- Generator still receives the current strategy and natural argument. Its **within-round**
  prior code, Lean errors, and Repair retry guidance remain available.
- All detailed history is still saved to logs even when withheld from Orchestrator input.
- Each independent execution starts with empty cross-round history in either condition.

This is an **input removal** experiment, not a separately optimized no-history prompt.
The ordinary historical `none` switch also changes some instructions; this experiment instead
freezes instruction selection to `use_memory=True` while gating `trial_memory` to empty.
The source snapshots in `source_full/` and `source_none/` retain the evaluated difference:
11 critical files are identical, and `goal_search.py` implements the data-only adjustment.
Do not assume a fresh invocation of an unmodified `--memory-conditions none` flag reproduces
this exact ablation. Consult `original121_ablation/experiment_notes.txt`, the source snapshots,
and the archived runtime before reproducing it.

Offline and logged checks establish identical first-round inputs and instructions across
conditions, with only `trial_memory` differing in later-round Orchestrator input. Outputs
are independently sampled, including round 1; they are not shared/cached across conditions.

## Accuracy: first complete execution only

| Cohort | Mode | History full | History none | Full − none |
|---|---|---:|---:|---:|
| Original121 | Single | 78/121 · 64.5% | 71/121 · 58.7% | +7 · +5.8 pp |
| | Dual | 80/121 · 66.1% | 72/121 · 59.5% | +8 · +6.6 pp |
| New29 | Single | 9/29 · 31.0% | 11/29 · 37.9% | −2 · −6.9 pp |
| | Dual | 11/29 · 37.9% | 9/29 · 31.0% | +2 · +6.9 pp |
| **Full150** | **Single** | **87/150 · 58.0%** | **82/150 · 54.7%** | **+5 · +3.3 pp** |
| | **Dual** | **91/150 · 60.7%** | **81/150 · 54.0%** | **+10 · +6.7 pp** |
| Selected144 | Single | 86/144 · 59.7% | 77/144 · 53.5% | +9 · +6.3 pp |
| | Dual | 90/144 · 62.5% | 77/144 · 53.5% | +13 · +9.0 pp |

**Selection disclosure:** selected144 = original121 + 23 retained Judson problems. Six new
problems were removed after inspecting Single-only/no-history-only successes. These exclusions
directly favor the targeted comparisons; selected144 is a development/exploratory subset,
not an independent final test or an unbiased memory-effect estimate. The unfiltered full150
records and all six excluded IDs remain available. See
[selection details](../../data/book144_posthoc_v1/README.md).

Exploratory exact paired McNemar results:

| Cohort | Mode | Full-only correct | None-only correct | Two-sided p |
|---|---|---:|---:|---:|
| Original121 | Single | 14 | 7 | 0.1892 |
| | Dual | 13 | 5 | 0.0963 |
| Full150 | Single | 16 | 11 | 0.4421 |
| | Dual | 18 | 8 | 0.0755 |

Full150 point estimates favor history, but neither paired test reaches 0.05. These exploratory
tests are not adjusted for multiple comparisons. Selected144 p-values in the machine tables
are descriptive only: outcome-based exclusions invalidate their use as confirmatory evidence.
Independent sampling, one execution per condition, previously inspected problems, and different
run dates limit causal/generalization claims. The 29 added problems are all true abstract-algebra
statements, changing both class and subject mixture.

## Reference-length groups and per-problem joins

`cohort_memory_accuracy.csv` covers original121, new29, retained23, selected144, and full150.
It includes paired discordant counts, rates, percentage-point changes, and exploratory p-values.
Length groups are supplied for original121 and selected144 using the fixed **reference** proof
body lengths from the full-memory report: 40/41/40 and 48/48/48 respectively. Generated proof
length does not determine these bins. The historical new29-specific groups are also retained.

| Cohort | Reference group | Single full | Single none | Dual full | Dual none |
|---|---|---:|---:|---:|---:|
| Original121 | Short · 40 | 39 | 37 | 38 | 38 |
| | Medium · 41 | 28 | 29 | 29 | 27 |
| | Long · 40 | 11 | 5 | 13 | 7 |
| Selected144 | Short · 48 | 46 | 44 | 46 | 44 |
| | Medium · 48 | 28 | 27 | 29 | 26 |
| | Long · 48 | 12 | 6 | 15 | 7 |

`paired_problem_memory_results.csv` has one row per ID and four success flags:
`single_full_correct`, `single_none_correct`, `dual_full_correct`, `dual_none_correct`.
`scored_runs_for_join.jsonl` contains all 600 scored rows with explicit `memory_condition`,
integer `repetition=1`, original121/new29 cohort, and `retained144` flags.

Join to [full-memory repeated runs](../book144_full_pass3_20261020/scored_runs_for_join.jsonl)
by `(id, mode, memory_condition, repetition)`. The full-memory repetition1 rows are reused
historical observations, not additional independent runs; deduplicate them. Do not fabricate
none repetitions2/3 or treat quarantined attempts as extra pass@k samples.

## Models, budgets, and usage

Orchestrator: `openai/gpt-6-luna-pro`; Natural/Generator/Repair: `openai/gpt-6-luna`.
Route pinned to `openai/flex`, no model/provider fallback. Three rounds, three Lean trials per lane.
Single has at most 9 Lean attempts per execution; Dual at most 18. The architectures therefore
have different maximum verification/token/cost budgets even though pipeline-run counts match.

`baseline.env` is non-secret configuration. `plan.json`, public inputs, evaluator-only labels,
source snapshots and offline checks preserve the evaluated setup. See the
[final pipeline](../../docs/FINAL_PIPELINE.md) for role/memory boundaries.

`usage_full/` and `usage_none/` contain call-level CSV/JSONL, agent/round/problem summaries,
tokens (including provider-reported reasoning/cached fields where available), provider-reported
USD cost and consistency checks against run aggregates. `original121_ablation/` additionally
retains its earlier complete analysis, strategy-input traces and separate infrastructure usage.
Costs are recorded historical provider values, not current price-list estimates.

## Infrastructure failures were retried

The original121 no-history experiment encountered **42 quarantined attempts across 26 unique
problem/mode executions**, in 12 incident groups. All were retained and rerun; all canonical
replacements completed without call errors. See
`original121_ablation/infra_retry_integrity.json`, `call_error_audit.json`, and
`infrastructure_overhead.json`. The 42 are infrastructure-affected attempts, not 42 final failures.

The added29 experiment completed all 116 new executions with zero call-error-held rows and no
quarantined new executions. Its root `infra_retry_integrity.json` describes **the extension only**;
it does not erase the earlier 42 attempts. Original121 infrastructure overhead was reported
separately as $0.77289148; missing provider usage is not certified as free.

Canonical accuracy is computed from clean completed executions, not from outage-affected attempts.
Health probes and discarded attempts are not counted as dataset problems or repeated samples.

The publication re-audited every canonical raw log: 300 full runs and 300 none runs.
All **930 no-history Orchestrator calls**, including **480 later-round calls**, have empty history
inputs and unchanged baseline instructions. All 907 full-condition Planner calls have matching
instructions; later-round history is present only in full. The 600 canonical event logs have no
API exception, provider-error response or empty-choice response. See `planner_input_audit.json`.
This audit reads saved logs only and makes no model calls.

## Files and downloads

- `runs_full.jsonl`, `runs_none.jsonl`: 300 scored rows each, all 150 IDs × two modes.
- `summary.json`, `paired_results.csv`, `by_field` content: saved full150 analysis.
- `posthoc_filtered150/`: historical filename for the **144 retained** subset; its README disclosure
  is supplemented above and its ID/selection files are retained.
- `original121_ablation/`: original121 no-history analysis, checks, traces, sources and usage.
- `publication_provenance.json`: original/public hashes; `public_sha256.json`: public file hashes.
- `original_local_verification.json`: preserved pre-publication archive/table verification.

The [GitHub Release](https://github.com/lee-young-jik/Proposal-of-an-LLM-Lean-Approach-and-Architecture-for-Math-Problem-Solving/releases/tag/memory-ablation-150-20261021)
includes full150 full-memory and no-memory raw archives, infrastructure supervision logs, and
a downloadable public-tables bundle. The full150 no-memory archive includes the original121
and new29 canonical no-history runs, so downloading a duplicate121 canonical archive is unnecessary.

Raw archives preserve agent instructions/inputs, outputs, provider responses/usage, strategy and
natural reasoning, generated Lean, diagnostics, Repair feedback, manifests, outcomes and source
snapshots. Supervision logs preserve the 42 quarantined attempts and health probes. Private machine
paths are normalized in public copies; authentication keys and root `.env` files are excluded.
Original local files remain unchanged. Embedded original hashes are historical provenance;
`PUBLICATION_MANIFEST.json` maps original to public per-file hashes inside each public archive.

Validate public tables without paid model calls:

```bash
python scripts/verify_memory_comparison_results.py
```
