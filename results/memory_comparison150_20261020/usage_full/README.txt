Detailed API usage from original audit events.
api_calls.csv: one row per actual API request, including rejected/retried calls.
by_agent.csv: totals for each architecture and role.
by_round_agent.csv: architecture/round/role totals.
by_problem_agent.csv: problem/architecture/role totals.
raw_usage.jsonl: provider usage payload, preserving all returned fields.
Empty per-call fields mean not returned, not necessarily zero. Aggregates sum reported values.
Costs are provider-reported USD; reasoning/cached tokens are token subcategories, not additional to the input/output totals.
Original full prompts, responses, Lean code/errors and Repair guidance remain in each audit_dir/events.jsonl.
No credentials are exported. Cost/input/output totals are checked against the original run records.
