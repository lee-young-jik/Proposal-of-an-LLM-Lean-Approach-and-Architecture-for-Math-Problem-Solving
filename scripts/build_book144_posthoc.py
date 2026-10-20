"""Build/check the disclosed outcome-selected subset; no model calls."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
PARENT=ROOT/'data/book150_v1'
OUT=ROOT/'data/book144_posthoc_v1'
EXCLUDED={'judson_11_4_12','judson_11_4_16','judson_3_5_26',
          'judson_4_5_39','judson_4_5_44','judson_4_5_45'}


def read(path):
    return [json.loads(line) for line in path.read_text(encoding='utf-8').splitlines() if line.strip()]


def canonical(text):return text.replace('\r\n','\n').encode('utf-8')
def digest(data):return hashlib.sha256(data).hexdigest()


def main(check=False):
    source=read(PARENT/'problems.jsonl');labels=read(PARENT/'labels.jsonl')
    selection=json.loads((OUT/'selection.json').read_text(encoding='utf-8'))
    assert set(selection['excluded_ids'])==EXCLUDED and len(selection['excluded_ids'])==6
    assert selection['posthoc_outcome_selected'] and selection['not_independent_final_test']
    assert len(source)==len(labels)==150
    assert {r['name'] for r in source}=={r['id'] for r in labels}
    assert EXCLUDED<={r['name'] for r in source}
    problems=[{**r,'split':'book144_posthoc_v1'} for r in source if r['name'] not in EXCLUDED]
    answers=[r for r in labels if r['id'] not in EXCLUDED]
    assert len(problems)==len(answers)==144
    ids={r['name'] for r in problems}
    assert len(ids)==144 and ids=={r['id'] for r in answers}
    old_ids={r['name'] for r in read(ROOT/'data/book121_v1/problems.jsonl')}
    assert old_ids<=ids and len(ids-old_ids)==23
    forbidden={'truth_label','verified_task','lean_proof','certificate','gold_proof_lines','gold_length_class'}
    assert all(not forbidden.intersection(r) for r in problems)
    assert sum(r['truth_label'] for r in answers)==65
    artifacts={
        'problems.jsonl':canonical(''.join(json.dumps(r,ensure_ascii=False)+'\n' for r in problems)),
        'labels.jsonl':canonical(''.join(json.dumps(r,ensure_ascii=False)+'\n' for r in answers)),
        'excluded_ids.txt':canonical('\n'.join(sorted(EXCLUDED))+'\n'),
        'ids.txt':canonical('\n'.join(sorted(ids))+'\n')}
    manifest={'dataset':'book144_posthoc_v1','problem_count':144,'true':65,'false':79,
              'origin_counts':dict(Counter(r['dataset_origin'] for r in answers)),
              'field_counts':dict(Counter(r['book_key'] for r in answers)),
              'parent_dataset':'book150_v1','parent_problem_count':150,
              'parent_files_sha256':{n:digest(canonical((PARENT/n).read_text(encoding='utf-8')))
                                     for n in ('problems.jsonl','labels.jsonl')},
              'posthoc_outcome_selected':True,'not_independent_final_test':True,
              'selection_metadata':'selection.json','hash_line_endings':'UTF-8 LF',
              'files':{**{n:digest(data) for n,data in artifacts.items()},
                       'selection.json':digest(canonical((OUT/'selection.json').read_text(encoding='utf-8')))}}
    artifacts['manifest.json']=canonical(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
    for name,data in artifacts.items():
        path=OUT/name
        if check:assert path.exists() and canonical(path.read_text(encoding='utf-8'))==data,name
        else:path.write_bytes(data)
    print(json.dumps({'checked' if check else 'built':str(OUT.relative_to(ROOT)),
                      'problems':144,'true':65,'false':79,'original121_retained':121,
                      'new_judson_retained':23,'excluded':6,'posthoc_outcome_selected':True}))


if __name__=='__main__':
    parser=argparse.ArgumentParser(__doc__);parser.add_argument('--check',action='store_true')
    main(parser.parse_args().check)
