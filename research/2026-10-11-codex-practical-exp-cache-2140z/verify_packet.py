#!/usr/bin/env python3
"""Public byte/evidence verifier. Runs no compiler, solver or benchmark."""
from pathlib import Path
import csv, hashlib, json, statistics

ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[1]
EVIDENCE=ROOT/'evidence'
def sha(data):return hashlib.sha256(data).hexdigest()
def check(condition,message):
    if not condition:raise ValueError(message)

manifest=json.loads((ROOT/'MANIFEST.json').read_text())
for row in manifest['files']:
    file=ROOT/row['path'];data=file.read_bytes()
    check(len(data)==row['bytes'] and sha(data)==row['sha256'],row['path'])
    blob=hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()
    check(blob==row['git_blob_sha1'],'blob '+row['path'])
expected={row['path'] for row in manifest['files']}|{'MANIFEST.json'}
actual={str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file()}
check(actual==expected,'unexpected/missing packet files')

check(json.loads((EVIDENCE/'RESULT.json').read_text())['status']=='PASS','result')
pins=json.loads((EVIDENCE/'source-pins-before.json').read_text())
check(pins==json.loads((EVIDENCE/'source-pins-after.json').read_text()),'source pins changed')
for name,want in pins.items():check(sha((REPO/name).read_bytes())==want,'source '+name)
for row in json.loads((EVIDENCE/'execution.json').read_text()):
    label=row['label']
    check(row['exit']==(101 if label.startswith('mutation-') else 0),'exit '+label)
    for suffix in ['stdout','stderr']:
        data=(EVIDENCE/(label+'.'+suffix)).read_bytes()
        check(sha(data)==row[suffix+'_sha256'],label+' '+suffix)
    if label.startswith('mutation-'):
        check(b'test result: FAILED' in (EVIDENCE/(label+'.stdout')).read_bytes(),'mutation assertion '+label)
for row in json.loads((EVIDENCE/'mutations.json').read_text()):
    check(sha((EVIDENCE/'mutant-sources'/(row['name']+'.rs')).read_bytes())==row['mutated_source_sha256'],
          'exact mutant source '+row['name'])

base=REPO/'research/2026-10-08-cloud-rust-interval-root-0000z/reports/cloud-differential/run-once'
want=(base/'probe.stdout.tsv').read_bytes()
for row in json.loads((EVIDENCE/'corpus.json').read_text()):
    check((EVIDENCE/(row['label']+'.stdout')).read_bytes()==want,'corpus '+row['label'])
    check(row['exact_matches']==3048 and row['actual_rows']==3048 and not row['differences'],'corpus rows')

benches=json.loads((EVIDENCE/'benchmarks.json').read_text())
for index,item in enumerate(benches):
    workload=item['workload'];capacity=item['cache_capacity'];output=None
    check(sha((EVIDENCE/f'bench-input-{index}.tsv').read_bytes())==item['input_sha256'],'literal workload input')
    for cap in [0,capacity]:
        rows=[]
        for round_number in range(3):
            label=f'bench-{index}-{workload}-cap{cap}-round{round_number}'
            rows.extend(list(csv.DictReader((EVIDENCE/(label+'.stdout')).read_text().splitlines(),delimiter='\t')))
            data=(EVIDENCE/(label+'.stderr')).read_bytes()
            if output is None:output=data
            check(data==output,'exact benchmark output')
        check(len(rows)==9,'repetitions')
        for key,want_median in item['modes'][str(cap)].items():
            check(statistics.median(int(row[key.removeprefix('median_')]) for row in rows)==want_median,'median '+key)
        label=f'alloc-{index}-{workload}-cap{cap}'
        check((EVIDENCE/(label+'.stderr')).read_bytes()==output,'allocation-mode output')
        alloc=list(csv.DictReader((EVIDENCE/(label+'.stdout')).read_text().splitlines(),delimiter='\t'))[0]
        for key,value in item['separate_allocation_measurement'][str(cap)].items():
            check(int(alloc[key])==value,'allocation '+key)
    check(sha(output)==item['output_sha256'],'benchmark output hash')
print(f"PASS: {len(manifest['files'])+1} packet files; exact corpus outputs, receipt hashes, medians, allocations and mutation assertions. No compiler replay.")
