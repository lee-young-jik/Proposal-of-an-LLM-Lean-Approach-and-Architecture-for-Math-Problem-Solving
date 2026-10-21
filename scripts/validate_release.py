"""Validate the self-contained 137-problem release without model/Lean calls."""
import hashlib
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data/book137_posthoc_v1'
RESULTS = ROOT / 'results/book137_pass5'

def read(path):
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]

def main():
    manifest = json.loads((DATA / 'manifest.json').read_text())
    for name, expected in manifest['sha256'].items():
        assert hashlib.sha256((DATA / name).read_bytes()).hexdigest() == expected, name
    problems = read(DATA / 'problems.jsonl')
    labels = {r['id']: r for r in read(DATA / 'labels.jsonl')}
    refs = {r['id']: r for r in read(DATA / 'reference_answers.jsonl')}
    ids = {r['name'] for r in problems}
    assert len(problems) == len(ids) == len(labels) == len(refs) == 137
    assert ids == set(labels) == set(refs) == set((DATA / 'ids.txt').read_text().splitlines())
    assert sum(r['truth_label'] for r in labels.values()) == 62
    forbidden = {'truth_label', 'verified_task', 'lean_proof', 'lean_code', 'certificate',
                 'gold_proof_lines', 'gold_length_class', 'selection'}
    assert all(not forbidden.intersection(r) for r in problems)
    assert all(r['split'] == 'book137_posthoc_v1' for r in problems)
    for i in ids:
        assert refs[i]['truth_label'] == labels[i]['truth_label']
        assert refs[i]['verified_task'] == labels[i]['verified_task']
        assert refs[i]['lean_code'] and labels[i]['gold_proof_lines'] > 0
    selection = json.loads((DATA / 'selection.json').read_text())
    assert set(selection['retained_ids']) == ids
    assert selection['posthoc_outcome_selected'] and selection['not_independent_holdout']
    rows = read(RESULTS / 'per_execution.jsonl')
    assert len(rows) == 1370
    keys = {(r['id'], r['mode'], r['logical_repetition']) for r in rows}
    assert keys == {(i, m, k) for i in ids for m in ('single', 'dual') for k in range(1, 6)}
    for r in rows:
        assert r['expected_task'] == labels[r['id']]['verified_task']
        assert bool(r['correct']) == (r['prediction'] == r['expected_task'])
    summary = json.loads((RESULTS / 'summary.json').read_text())
    groups = json.loads((RESULTS / 'length_groups.json').read_text())
    assert [len(groups[k]) for k in ('short', 'medium', 'long')] == [48, 45, 44]
    assert set().union(*(set(v) for v in groups.values())) == ids
    first = {}
    for mode in ('single', 'dual'):
        for i in ids:
            rs = sorted((r for r in rows if r['id'] == i and r['mode'] == mode), key=lambda r: r['logical_repetition'])
            first[i, mode] = next((r for r in rs if r['correct']), None)
        solved = [first[i, mode] for i in ids if first[i, mode]]
        expected = summary['matrix'][mode]
        assert len(solved) == expected['correct']
        assert sum(r['prediction'] == 'prove' for r in solved) == expected['proved']
        assert sum(r['prediction'] == 'disprove' for r in solved) == expected['disproved']
        assert 137 - len(solved) == expected['unsolved']
    for table in summary['length_rows']:
        gi = ids if table['group'] == 'all' else groups[table['group']]
        for mode in ('single', 'dual'):
            values = [first[i, mode]['model_lines']/labels[i]['gold_proof_lines'] for i in gi if first[i, mode]]
            assert len(values) == table[mode]['correct']
            assert math.isclose(sum(values)/len(values), table[mode]['ratio'], rel_tol=1e-12)
    for mode, expected in [('single', [66, 30, 10]), ('dual', [77, 25, 7])]:
        assert [sum(bool(first[i, mode]) and first[i, mode]['rounds'] == k for i in ids) for k in (1, 2, 3)] == expected
    print('Validated 137 inputs, 62 Prove/75 Disprove, separate references, hashes and 1,370 records.')
    print('Pass@5: Single 106/137, Dual 109/137. Code-length and round tables match.')
    print('No model calls, new Lean certification or raw-usage verification performed.')

if __name__ == '__main__':
    main()
