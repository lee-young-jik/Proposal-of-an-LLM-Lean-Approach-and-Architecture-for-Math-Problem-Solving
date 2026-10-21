"""Verify published full-memory pass@3 outcomes and file hashes without model calls."""
import csv
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
RESULT=ROOT/'results/book144_full_pass3_20261020'

def lines(path):
    return [json.loads(s) for s in path.read_text(encoding='utf-8-sig').splitlines() if s.strip()]

def main():
    rows=lines(RESULT/'runs.jsonl')
    index={(r['id'],r['mode'],int(r['repetition'])):r for r in rows}
    ids={r['id'] for r in rows}
    assert len(rows)==len(index)==864 and len(ids)==144
    assert all(r['valid'] and not r.get('call_errors',0) and not r.get('infrastructure_errors',0) for r in rows)
    assert all((i,m,k) in index for i in ids for m in ('single','dual') for k in (1,2,3))
    assert ids=={r['name'] for r in lines(RESULT/'public_inputs.jsonl')}
    with (RESULT/'original121_reference_groups.csv').open(encoding='utf-8-sig') as f:
        old_groups={r['id']:r['group'] for r in csv.DictReader(f)}
    with (RESULT/'fixed_length_groups.csv').open(encoding='utf-8-sig') as f:
        all_groups={r['id']:r['group'] for r in csv.DictReader(f)}
    old=set(old_groups);assert len(old)==121 and len(ids-old)==23
    with (RESULT/'cohort_pass_at_k.csv').open(encoding='utf-8-sig') as f:
        for row in csv.DictReader(f):
            cohort=row['cohort'];k=int(row['k']);g=row['reference_group']
            chosen=old if cohort=='original121' else ids-old if cohort=='added23' else ids
            groups=old_groups if cohort=='original121' else all_groups
            if g!='all':chosen={i for i in chosen if groups[i]==g}
            s={i for i in chosen if any(index[i,'single',rep]['correct'] for rep in range(1,k+1))}
            d={i for i in chosen if any(index[i,'dual',rep]['correct'] for rep in range(1,k+1))}
            assert (len(chosen),len(s),len(d),len(s&d),len(s-d),len(d-s),len(chosen-s-d))==tuple(int(row[c]) for c in ('n','single_correct','dual_correct','both','single_only','dual_only','neither'))
    summary=json.loads((RESULT/'summary.json').read_text())
    assert summary['complete'] and summary['new_completed']==summary['new_expected']==576
    for curve in summary['curves']:
        k=curve['k'];g=curve['group']
        chosen=ids if curve['expected_problems']==144 else {i for i in ids if all_groups[i]==g}
        assert len(chosen)==curve['paired_completed_problems']==curve['expected_problems']
        for mode in ('single','dual'):
            assert sum(any(index[i,mode,rep]['correct'] for rep in range(1,k+1)) for i in chosen)==curve[mode+'_correct']
            for metric in ('input_tokens','output_tokens','actual_lean_checks','reported_cost_usd'):
                actual=sum(index[i,mode,rep][metric] for i in chosen for rep in range(1,k+1))
                assert abs(actual-curve[mode+'_'+metric])<1e-7
    integrity=json.loads((RESULT/'infra_retry_integrity.json').read_text())
    assert integrity['all_clean'] and integrity['quarantined']==len(integrity['verified'])==24
    usage=json.loads((RESULT/'usage/summary.json').read_text())
    assert usage['metrics_match_original_runs'] and usage['runs']==864 and usage['api_requests']==usage['api_responses']==18231
    original=lines(RESULT/'prior_memory_comparison150/runs_full.jsonl')
    for row in original:
        if row['id'] in ids:
            baseline=index[row['id'],row['mode'],1]
            for key in ('correct','input_tokens','output_tokens','actual_lean_checks','reported_cost_usd'):
                assert row[key]==baseline[key],(row['id'],row['mode'],key)
    hashes=json.loads((RESULT/'public_sha256.json').read_text())
    for name,expected in hashes.items():
        assert hashlib.sha256((RESULT/name).read_bytes()).hexdigest()==expected,name
    print('PASS: 864 unique clean runs; cohort/group pass@1-3; costs/tokens/Lean checks; 24 retries; prior baseline identity; public file hashes. No model calls.')

if __name__=='__main__':main()
