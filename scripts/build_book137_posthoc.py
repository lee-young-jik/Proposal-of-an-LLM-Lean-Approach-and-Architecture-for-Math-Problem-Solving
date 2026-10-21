"""Export/check the final outcome-selected 137-problem analysis dataset (offline)."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'data/book137_posthoc_v1'
PARENT = ROOT / 'data/book144_posthoc_v1'

def read(path):
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]

def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()

def jsonl(rows):
    return ''.join(json.dumps(r, ensure_ascii=False) + '\n' for r in rows).encode()

def build(check=False):
    selection = json.loads((OUT / 'selection.json').read_text())
    ids = set(selection['retained_ids'])
    assert len(ids) == 137 and selection['posthoc_outcome_selected']
    source = read(PARENT / 'problems.jsonl')
    problems = [{**r, 'split': 'book137_posthoc_v1'} for r in source if r['name'] in ids]
    labels = [r for r in read(PARENT / 'labels.jsonl') if r['id'] in ids]
    assert {r['name'] for r in problems} == {r['id'] for r in labels} == ids
    assert set(selection['excluded_ids']) == {r['name'] for r in source} - ids
    assert sum(r['truth_label'] for r in labels) == 62 and len(labels) == 137
    forbidden = {'truth_label', 'verified_task', 'lean_proof', 'lean_code', 'certificate',
                 'gold_proof_lines', 'gold_length_class', 'selection'}
    assert all(not forbidden.intersection(r) for r in problems)
    refs = read(ROOT / 'data/book121_v1/ground_truth/labels.jsonl')
    refs += read(ROOT / 'data/judson29_gold_v1/labels.jsonl')
    references = [{k: r[k] for k in ('id', 'truth_label', 'verified_task', 'lean_proof',
                                    'lean_code', 'certificate_sha256', 'axioms') if k in r}
                  for r in refs if r['id'] in ids]
    assert {r['id'] for r in references} == ids and len(references) == 137
    label_map = {r['id']: r for r in labels}
    for r in references:
        assert r['truth_label'] == label_map[r['id']]['truth_label']
    files = {'problems.jsonl': jsonl(problems), 'labels.jsonl': jsonl(labels),
             'reference_answers.jsonl': jsonl(references),
             'ids.txt': ('\n'.join(sorted(ids)) + '\n').encode(),
             'excluded_ids.txt': ('\n'.join(sorted(selection['excluded_ids'])) + '\n').encode()}
    manifest = {'dataset': 'book137_posthoc_v1', 'problem_count': 137,
                'prove': 62, 'disprove': 75, 'parent_dataset': 'book144_posthoc_v1',
                'book_counts': dict(Counter(r['book_key'] for r in labels)),
                'posthoc_outcome_selected': True, 'not_independent_holdout': True,
                'model_input': 'problems.jsonl',
                'evaluator_only': ['labels.jsonl', 'reference_answers.jsonl', 'selection.json'],
                'new_model_calls': False, 'new_lean_certification': False,
                'sha256': {k: hashlib.sha256(v).hexdigest() for k, v in files.items()}}
    manifest['sha256']['selection.json'] = hashlib.sha256((OUT / 'selection.json').read_bytes()).hexdigest()
    files['manifest.json'] = encode(manifest)
    for name, contents in files.items():
        if check:
            assert (OUT / name).read_bytes() == contents, name
        else:
            (OUT / name).write_bytes(contents)
    print(('Checked' if check else 'Exported') + ' 137 problems: 62 Prove / 75 Disprove; no model calls.')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--check', action='store_true')
    build(parser.parse_args().check)
