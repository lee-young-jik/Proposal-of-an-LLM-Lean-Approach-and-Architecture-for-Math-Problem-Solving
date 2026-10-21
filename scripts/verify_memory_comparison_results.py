"""Verify published full/none results; optionally audit every raw planner input."""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import zipfile

ROOT=Path(__file__).resolve().parents[1]
RESULT=ROOT/'results/memory_comparison150_20261020'

def lines(path):return [json.loads(s) for s in path.read_text(encoding='utf-8-sig').splitlines() if s.strip()]

def audit_archives(folder):
    instructions={};counts={};later={};runs={}
    for condition in ('full','none'):
        counts[condition]=0;later[condition]=0;runs[condition]=0
        with zipfile.ZipFile(folder/f'memory150_{condition}_raw_logs_20261020.zip') as archive:
            for name in archive.namelist():
                if not name.endswith('/events.jsonl') or not name.startswith('runs/'):
                    continue
                runs[condition]+=1
                mode=name.split('/')[2]
                events=[json.loads(s) for s in archive.read(name).decode().splitlines() if s.strip()]
                assert events[-1]['event']=='run_finished'
                for event in events:
                    assert event['event']!='api_error'
                    if event['event']=='api_response':
                        response=event.get('response') or {}
                        assert response.get('choices') and not response.get('error')
                    if event['event']!='node_started':continue
                    metadata=event.get('metadata',{});inputs=event.get('inputs',{})
                    if 'strategy' not in metadata.get('node',''):continue
                    key=(mode,metadata.get('task'));round_index=metadata['round']
                    if condition=='full':
                        if key in instructions:assert instructions[key]==metadata['instructions']
                        else:instructions[key]=metadata['instructions']
                        assert bool(inputs.get('trial_memory'))==(round_index>1)
                    else:
                        assert not inputs.get('trial_memory')
                        allowed=({'problem','goals'} if mode=='single' else {'problem','goal','assigned_task'})|{'lean_environment_declarations'}
                        assert inputs.keys()<=allowed
                        assert metadata['instructions']==instructions[key]
                    counts[condition]+=1;later[condition]+=int(round_index>1)
        assert runs[condition]==300
    assert len(instructions)==3
    return {'passed':True,'runs':runs,'planner_calls':counts,'later_round_planner_calls':later,
            'all_none_planner_inputs_history_free':True,'all_planner_instructions_identical':True,
            'canonical_raw_api_error_free':True,'model_calls':0}

def main():
    parser=argparse.ArgumentParser(__doc__)
    parser.add_argument('--raw-archives',type=Path)
    parser.add_argument('--write-raw-audit',type=Path)
    args=parser.parse_args()
    rows=lines(RESULT/'scored_runs_for_join.jsonl')
    index={(r['id'],r['mode'],r['memory_condition']):r for r in rows}
    ids={r['id'] for r in rows}
    assert len(rows)==len(index)==600 and len(ids)==150
    assert all(r['valid'] and int(r['repetition'])==1 for r in rows)
    assert all((i,m,c) in index for i in ids for m in ('single','dual') for c in ('full','none'))
    with (ROOT/'results/book144_full_pass3_20261020/original121_reference_groups.csv').open(encoding='utf-8-sig') as f:
        old_groups={r['id']:r['group'] for r in csv.DictReader(f)}
    with (ROOT/'results/book144_full_pass3_20261020/fixed_length_groups.csv').open(encoding='utf-8-sig') as f:
        selected_groups={r['id']:r['group'] for r in csv.DictReader(f)}
    old=set(old_groups);selected=set(selected_groups)
    cohorts={'original121':old,'new29':ids-old,'selected144':selected,'retained23':selected-old,'full150':ids}
    with (RESULT/'cohort_memory_accuracy.csv').open(encoding='utf-8-sig') as f:
        for row in csv.DictReader(f):
            chosen=cohorts[row['cohort']];mode=row['mode'];g=row['reference_group']
            if g!='all':
                groups=old_groups if row['cohort']=='original121' else selected_groups
                chosen={i for i in chosen if groups[i]==g}
            full={i for i in chosen if index[i,mode,'full']['correct']}
            none={i for i in chosen if index[i,mode,'none']['correct']}
            assert (len(chosen),len(full),len(none),len(full&none),len(full-none),len(none-full),len(chosen-full-none))==tuple(int(row[k]) for k in ('n','full_correct','none_correct','both_correct','full_only','none_only','neither'))
    summary=json.loads((RESULT/'summary.json').read_text())
    assert summary['complete'] and summary['new_completed']==summary['new_executions']==116
    for condition,key in (('full','with_history'),('none','without_history')):
        for mode in ('single','dual'):
            cell=summary[key][mode]
            chosen=[r for r in rows if r['mode']==mode and r['memory_condition']==condition]
            assert cell['completed']==cell['valid']==150 and cell['correct']==sum(r['correct'] for r in chosen)
            for metric in ('input_tokens','output_tokens','reported_cost_usd','actual_lean_checks'):
                assert abs(cell[metric]-sum(r[metric] for r in chosen))<1e-7
        usage=json.loads((RESULT/f'usage_{condition}/summary.json').read_text())
        assert usage['metrics_match_original_runs'] and usage['runs']==300
        assert usage['api_requests']==usage['api_responses']
        assert all(not r[k] for r in usage['by_agent'] for k in ('api_errors','provider_error_responses','no_response'))
    integrity=json.loads((RESULT/'original121_ablation/infra_retry_integrity.json').read_text())
    assert integrity['quarantined_attempts_verified']==42 and integrity['unique_affected_runs']==26
    assert integrity['all_retries_completed_without_call_errors']
    baseline=lines(ROOT/'results/book144_full_pass3_20261020/runs_rep1.jsonl')
    for row in baseline:
        before=index[row['id'],row['mode'],'full']
        for key in ('correct','reported_cost_usd','input_tokens','output_tokens','actual_lean_checks'):
            assert before[key]==row[key]
    for file in (RESULT/'source_full').iterdir():
        if file.name!='goal_search.py':assert file.read_bytes()==(RESULT/'source_none'/file.name).read_bytes()
    if args.raw_archives:
        audit=audit_archives(args.raw_archives)
        print(json.dumps(audit))
        if args.write_raw_audit:args.write_raw_audit.write_text(json.dumps(audit,indent=2)+'\n',encoding='utf-8')
    manifest=RESULT/'public_sha256.json'
    if manifest.exists():
        for name,expected in json.loads(manifest.read_text()).items():
            assert hashlib.sha256((RESULT/name).read_bytes()).hexdigest()==expected,name
    print('PASS: 600 scored rows; full/none cohorts and reference groups; usage totals; 42 infrastructure retries; pass3 historical baseline identity; frozen source boundaries. No model calls.')

if __name__=='__main__':main()
