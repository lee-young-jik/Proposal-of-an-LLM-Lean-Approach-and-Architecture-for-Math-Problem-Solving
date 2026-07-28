# Reproducibility Notes

## Evaluated task

The reported experiment uses sets 01–05. Each set contains 10 true statements
and 10 false statements. The full reported subset therefore contains 50 true
and 50 false statements.

Evaluation is Pass@1: every architecture is run once on every problem.

Lean verification runs in the pinned miniF2F checkout and therefore uses that
project's Lean 4.27.0 toolchain.

## Budget

| Setting | Single | Dual |
|---|---:|---:|
| Maximum strategy rounds | 3 | 3 |
| Maximum proof trials per round | 3 | 3 |
| Maximum Lean verification time | 300 seconds | 300 seconds |
| Passes per problem | 1 | 1 |

The historical launch scripts used no model-call timeout for sets 01–03 and a
900-second model-call timeout for sets 04–05. The public reproduction script
preserves this operational setting.

## Model routing

| Role | Route | Model |
|---|---|---|
| Orchestrator | Codex CLI OAuth | `gpt-5.4` |
| Lean Generator | Codex CLI OAuth | `gpt-5.4` |
| Natural Agent | OpenRouter | `openai/gpt-5.4-nano` |
| False Reasoner Agent | OpenRouter | `openai/gpt-5.4-nano` |
| Repair/Retry Agent | OpenRouter | `openai/gpt-5.4-nano` |

`--strict-model-routing` is always enabled. An absent route is an error; the
runtime must not silently choose a fallback model.

## False-decision protocol

At the end of a failed round, the False Reasoner Agent reads that round's
memory and returns:

```json
{
  "why": "the concrete mathematical reason",
  "change": "the inferred statement repair",
  "unclear": false
}
```

The Orchestrator-side conservative checker compares this diagnosis with the
private mutation key. It returns `false` only when both the mathematical error
and the repair match. Any vague, partial, different, or uncertain diagnosis
continues to the next round.

The False Reasoner Agent does not receive the mutation key.

## Historical and improved Dual memory layouts

The result files checked into `results/paper` were produced with the historical
layout:

```text
truth trial 1
truth trial 2
truth trial 3 + counter_reasoning from the Falsifier
```

This is selected with:

```bash
DUAL_ARC_DUAL_MEMORY_SCHEMA=paper_merged
```

After the reported experiment, the implementation was improved so that the
False Reasoner Agent receives two explicit sections:

```json
{
  "truth_memory": [],
  "falsifier_memory": []
}
```

This is selected with:

```bash
DUAL_ARC_DUAL_MEMORY_SCHEMA=separate
```

The separate-schema version has not been used to regenerate the reported
35/38 and 0/24 values. New results produced with it must be reported as a new
experiment rather than as the original paper run.

## Sources of unavoidable variation

- LLM sampling and provider-side serving are non-deterministic.
- Hosted model aliases may be updated after the experiment date.
- Timeouts and network errors can change the number of completed calls.
- OAuth and API usage limits can interrupt a run.

For this reason, reproduction should compare aggregate behavior and preserve
all output JSONL files rather than expect byte-identical responses.
