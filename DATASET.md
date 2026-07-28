# Dataset

## Public evaluation subset

The repository contains the five sets used in the reported experiment:

```text
data/set_01/
...
data/set_05/
```

Every directory contains:

- `mixed20.jsonl`: 20 model inputs
- `labels.jsonl`: gold labels and evaluator-only false-mutation keys

Each set has 10 true and 10 false statements. Across all five sets there are 50
true and 50 false statements.

## False-statement construction

Each false statement was produced by locally changing a true statement. Five
mutation types are used, with 10 examples of each type in sets 01–05:

1. `nearby_answer_constant`: replace the correct final value with a nearby
   value.
2. `equality_relation_flip`: replace an equality with a disequality, or reverse
   the polarity of a non-equality conclusion.
3. `strict_order_contradiction`: replace an exact equality with a strict order
   relation.
4. `trichotomy_branch_exclusion`: replace equality with the two strict branches
   that exclude equality.
5. `camouflaged_two_point_shift`: change the final value and add a logically
   irrelevant true condition to a premise.

## Evaluator-key isolation

`labels.jsonl` contains:

- `gold`
- `false_category`
- `false_transform`
- `expected_false_fix`

The model-facing problem loader reads `mixed20.jsonl`. The False Reasoner Agent
receives only trial memory. The private key is passed only to the final
conservative checker.

Although the evaluator keys are public for reproducibility, they must not be
included in model prompts or used to tune a response for an individual test
problem.

## Provenance

The statements were derived from the Lean 4 miniF2F corpus. The reproduction
script pins the upstream checkout to:

```text
https://github.com/google-deepmind/miniF2F
f0a20e14c1eeccd859d51bb4c2b3ee487889c303
```

Users should cite miniF2F and comply with the upstream repository's license and
terms.
