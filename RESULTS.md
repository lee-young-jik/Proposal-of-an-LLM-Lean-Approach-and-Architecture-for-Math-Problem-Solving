# Reported Results

## True statements

| Architecture | Solved | Not Solved | Mean Rounds to Solve |
|---|---:|---:|---:|
| Single | 35 | 15 | 1.14 |
| Dual | 38 | 12 | 1.16 |

## False statements

| Architecture | Detected as False | Not Solved | False Positives |
|---|---:|---:|---:|
| Single | 0 | 50 | 0 |
| Dual | 24 | 26 | 0 |

The tables can be regenerated from the checked-in JSONL files:

```bash
python scripts/summarize_results.py
```
