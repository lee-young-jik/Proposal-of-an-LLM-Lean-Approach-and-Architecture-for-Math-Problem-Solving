# Final 137-problem analysis dataset

논문의 최종 분석 대상 **137문제(Prove 62개, Disprove 75개)**입니다.
공개 입력과 평가용 정답을 분리했습니다. 코드와 프롬프트는 저장소의
`src/single_orchestrator/`에 있으며 실행 환경은
[CURRENT_SETUP.md](../../docs/CURRENT_SETUP.md)에 설명되어 있습니다.

## Files and model-input boundary

- `problems.jsonl`: natural-language statements, formal Prove statements, Lean preludes and source identifiers; split `book137_posthoc_v1`. The runtime constructs the corresponding Disprove goal. **Only this file is a model-input dataset.**
- `labels.jsonl`: evaluator-only Prove/Disprove labels and reference-length metadata.
- `reference_answers.jsonl`: evaluator-only reference proof bodies and complete Lean certificates, filtered from the existing 121/Judson reference releases.
- `ids.txt`: the 137 retained IDs.
- `excluded_ids.txt` and `selection.json`: exclusions and selection provenance; never model inputs.
- `manifest.json`: counts and SHA-256 hashes.

Do not send labels, reference answers or selection metadata to the agents.
Book source identifiers and original statements are retained. Original book
attribution and source links are available in the parent data releases; this
export does not change the underlying source licensing or redistribute textbooks.

## Selection and result provenance

This is the **final analysis version**, not a prospectively fixed independent
holdout. The 137 IDs were selected after inspecting the combined Pass@5 outcomes
and generated/reference code-length ratios of `book144_posthoc_v1`. Seven
Single-only successes were excluded (six from the original four books and one
Judson problem); their IDs remain in `selection.json`. The parent 144 set was
itself outcome-selected from 150. Original datasets and historical results remain
available rather than being overwritten.

The manuscript's final Pass@5 aggregation also replaces all five executions per
architecture for `calculus_23_3_10` and `book_of_proof_section_14_4_7` with a new
five-execution comparison after near-miss inspection. Original results and logs
are retained locally; revised reference proofs were not model inputs. For other
IDs the aggregation uses local repetitions 1–2 followed by the published GitHub
repetitions 1–3. These selection/replacement decisions limit generalization and
are not corrected by confidence intervals or significance tests.

The final aggregate is Single 106/137 and Dual 109/137. This release packages the
dataset and existing reference certificates; it does not perform new model calls
or new Lean certification, and does not bundle the local replacement-run logs.
Published historical run archives remain linked from the repository README.

## Prompts and settings

- [Actual two-goal prompts](../../src/single_orchestrator/goal_prompts.py)
- [Goal selection, memory and execution flow](../../src/single_orchestrator/goal_search.py)
- [Model/provider/budget configuration](../../configs/two_goal_experiment.env)
- [Role and memory contracts](../../docs/FINAL_PIPELINE.md)
- [Installation and pinned Lean/Mathlib environment](../../docs/CURRENT_SETUP.md)

Single selects a goal each round; Dual retains both goals. Both use at most
3 rounds and 3 Lean attempts per lane per round. Pass@5 means five independent
complete executions, with memory reset between executions. The comment
"Pass@1 evaluation budget" in the shared config describes one execution's
internal budget, not the number of repetitions.

## Offline validation and plan

```bash
python scripts/build_book137_posthoc.py --check
```

After installing the dependencies in the setup guide, this command writes a plan
for all 137 problems, both architectures and five repetitions (1,370 executions),
**without making model calls**:

```bash
python scripts/run_logged_experiment.py \
  --jsonl data/book137_posthoc_v1/problems.jsonl --split book137_posthoc_v1 \
  --ids $(cat data/book137_posthoc_v1/ids.txt) \
  --project-root .datasets/miniF2F-lean4 \
  --config-env configs/two_goal_experiment.env \
  --repetitions 5 --memory-conditions full \
  --output-dir .runs/book137_plan
```

To run a fresh paid experiment, explicitly append `--run` and use a new output
directory. A new stochastic run is not expected to reproduce the manuscript's
historical outcomes exactly. Grade offline with `scripts/analyze_logged_experiment.py`
using this directory's `labels.jsonl` and `problems.jsonl` as metadata.
