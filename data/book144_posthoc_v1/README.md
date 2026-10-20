# Selected 144-problem dataset

This version retains all 121 original textbook problems and 23 of the 29 Judson
problems: **144 unique problems, 65 true and 79 false**. It removes six problems
from [the original 150-problem dataset](../book150_v1/README.md).

**Selection was made after observing evaluation outcomes.** The six problems
were selected because Single succeeded while Dual failed under full memory,
or because a no-history run succeeded while the same architecture's full-memory
run failed. This is an outcome-selected subset for development and exploratory
analysis, **not an independent final test set or an unbiased estimate of Dual
or memory superiority**. No dataset defect was established by those outcomes.
The original 150 inputs and reference answers are preserved; full evaluation
results remain local. Subset scores must not replace the full-set result.

## Exclusions

Rules apply only to the 29 new problems, with one complete pipeline execution
per architecture/condition. `full` supplies previous-round Orchestrator memory;
`none` removes that input with the same system instructions.

| Observed outcome | Excluded IDs |
|---|---|
| Single full correct, Dual full incorrect | `judson_4_5_44` |
| Single full incorrect, Single none correct | `judson_11_4_12`, `judson_11_4_16`, `judson_3_5_26`, `judson_4_5_45` |
| Dual full incorrect, Dual none correct | `judson_11_4_16`, `judson_4_5_39`, `judson_4_5_44` |

The categories contain 1, 4 and 3 problems; their union has **six** unique IDs.
These observed differences do not establish that memory caused a failure.
The memory conditions have independent outputs, including first-round attempts.

## Files

- `problems.jsonl`: public model inputs; split `book144_posthoc_v1`.
- `labels.jsonl`: evaluator-only labels and reference-length metadata.
- `ids.txt` / `excluded_ids.txt`: retained and excluded problem IDs.
- `selection.json`: selection rules, observed outcomes and provenance.
- `manifest.json`: counts, source and file hashes (canonical UTF-8 LF).

Do not send labels, selection metadata or reference proofs to evaluation agents.
Public statements, goals and preludes are unchanged from the parent dataset;
only split names are updated. Reference certificates remain in
[book121 ground truth](../book121_v1/ground_truth/README.md) and
[Judson ground truth](../judson29_gold_v1/README.txt); select by `ids.txt`.
This release performs no new Lean certification or model calls.

## Rebuild and check

```bash
python scripts/build_book144_posthoc.py
python scripts/build_book144_posthoc.py --check
```

Follow [the setup guide](../../docs/CURRENT_SETUP.md). Plan-only example:

```bash
python scripts/run_logged_experiment.py \
  --jsonl data/book144_posthoc_v1/problems.jsonl --split book144_posthoc_v1 \
  --ids linear_algebra_6A_24 judson_9_4_8 \
  --project-root .datasets/miniF2F-lean4 \
  --config-env configs/two_goal_experiment.env \
  --repetitions 1 --memory-conditions full \
  --output-dir .runs/book144_plan
```
