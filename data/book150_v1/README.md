# 150-problem Lean dataset

The evaluation set combines the existing 121 textbook problems with 29 proof
problems from Thomas W. Judson's *Abstract Algebra: Theory and Applications*.
It contains **150 unique targets: 71 true and 79 false**.

| Origin | Problems | True | False |
|---|---:|---:|---:|
| Existing textbook set | 121 | 42 | 79 |
| Judson abstract algebra | 29 | 29 | 0 |
| Total | 150 | 71 | 79 |

## Files and reference answers

- [problems.jsonl](problems.jsonl): public CLI inputs, with split `book150_v1`.
- [labels.jsonl](labels.jsonl): evaluator-only truth labels, origin, and reference
  proof lengths. Do not provide this file to evaluation agents.
- [manifest.json](manifest.json): counts and SHA-256 hashes of both JSONL files.
- [Existing 121 reference answers](../book121_v1/ground_truth/README.md): labels,
  complete Lean certificates, and certification metadata.
- [Judson 29 reference answers](../judson29_gold_v1/README.txt): labels, complete
  Lean certificates, axiom checks, and proof lengths.
- [Judson paired goals](../judson29_goals_v1/README.txt): original source links,
  formalization decisions, 29 prove goals and their exact whole-goal negations.

The 29 new targets are all true proof problems. Their disprove goals are search
alternatives, not 29 additional dataset examples. References to textbook pages
and formalization choices are preserved in the accompanying metadata.

## Reference proof lengths

Count nonblank, noncomment lines in the reference proof body, excluding imports
and theorem headers: short ≤10, medium 11–30, long ≥31. These are code lengths,
not mathematical difficulty or shortest-proof measurements.

| Origin | Short | Medium | Long |
|---|---:|---:|---:|
| Existing 121 | 64 | 29 | 28 |
| Judson 29 | 18 | 7 | 4 |
| Total | 82 | 36 | 32 |

## Evaluation protocol

Pass@5 uses five independent **complete pipeline executions** per problem and
architecture. Each execution retains at most three strategy rounds and three
attempts per round per lane: at most nine attempts for Single and eighteen for
Dual. A verified solution may end an execution early; all five independent
executions are still scheduled with fresh memory. Pass@1 is reported separately
from these five repetitions.

API failures and empty responses are preserved in local recovery logs and
retried; they do not consume a valid repetition or count as mathematical errors.
Raw evaluation logs and unfinished results are not part of this dataset release.
See [the final pipeline](../../docs/FINAL_PIPELINE.md) for role and memory details.

Report the whole set and the old/new and proof-length subgroups separately.
This set includes development problems and an exploratory new selection; it is
not an untouched holdout and does not establish a Dual advantage by selection.
