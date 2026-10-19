# Portable 121-problem inputs

`problems.jsonl` contains public, ProofNet-compatible inputs for the current CLI.
It preserves the natural-language statement, original prove header and Lean
prelude from the locally verified textbook dataset. Refutation targets are
derived as the negation of the complete prove goal by the current runtime.

`labels.jsonl` contains evaluator-only Boolean answers and direction labels:
42 true, 79 false. Do not pass this file to the model runner. Full answer explanations and Lean certificates are published separately in
[ground_truth/](ground_truth/README.md). Raw source PDFs and local model-run
logs are not included.
These are excerpts of problems from Book of Proof, Basic Analysis, Linear
Algebra Done Right and the calculus sources described by each problem ID;
this export is a format conversion, not a new answer certification or an
independent semantic review.

`balanced22_ids.txt` records the fixed 11-true/11-false exploratory subset.
Six goals in that subset had already appeared in local development runs; it
is not a completely unseen final test set. Keep the original scores separate
from new runs. `manifest.json` records counts and file hashes.

See [the setup guide](../../docs/CURRENT_SETUP.md) for running and grading.
