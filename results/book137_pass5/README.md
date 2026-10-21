# Final 137-problem Pass@5 analysis

`per_execution.jsonl` contains 1,370 scored records (137 problems × two architectures
× five executions), normalized to remove run identifiers and private audit paths.
`summary.json` preserves the manuscript aggregates; `paired_statistics.json` contains
exploratory paired tests; `length_groups.json` freezes the 48/45/44 reference-length bins.
These bins are separate from the historical `gold_length_class` labels.

The same problem's repetitions are not separate independent dataset problems.
Pass@5 counts at least one correct execution. Code length uses the first correct
execution in logical repetition order, separately for each architecture. Reported
lengths are nonblank/noncomment proof-body lines divided by reference proof-body lines.
The ordinary table uses each architecture's own successful set; the paired analysis
uses the 106 common successes. Original model-generated code and API/Lean raw logs
are not included here, so this package recomputes numerical aggregates but does not
independently reverify every historical generated proof or reconstruct API usage.

Selection and two-problem five-run replacement are documented in
[the dataset](../../data/book137_posthoc_v1/README.md). The bootstrap intervals do not
correct outcome-based selection. Reported resource values include recorded API usage
only, exclude unavailable usage (Single 41 responses, Dual 91), and exclude discarded
and pre-replacement runs. They are not total project expenditure.

```bash
python scripts/validate_release.py
```
