#!/usr/bin/env python3
"""Capture complete completed-batch compiler evidence without binary objects."""
import argparse
import base64
import hashlib
import json
from pathlib import Path

LOADED_SHA=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

def sha(data):return hashlib.sha256(data).hexdigest()

def inventory(state):
    return {p.name:sha(p.read_bytes()) for suffix in ['json','stdout','stderr']
            for p in sorted(state.glob('[0-9][0-9][0-9][0-9].'+suffix))}

def capture(state,batch,check_existing=False):
    terminal=json.loads((batch/'RECEIPT.json').read_text())
    for suffix in ['stdout','stderr']:
        data=(batch/suffix).read_bytes()
        if terminal['outputs'][suffix]!={'bytes':len(data),'sha256':sha(data)}:
            raise ValueError('guard output bytes differ: '+suffix)
    events=[]
    for line in (batch/'stdout').read_text().splitlines():
        try:row=json.loads(line)
        except json.JSONDecodeError:continue
        if isinstance(row,dict) and 'index' in row and 'module' in row:events.append(row)
    rows=[]
    for event in events:
        stem=f"{event['index']:04d}"
        data=(state/(stem+'.json')).read_bytes();receipt=json.loads(data)
        if receipt['module']!=event['module'] or receipt['exit_code']!=event['exit_code']:
            raise ValueError('batch output/receipt mismatch')
        row=dict(index=event['index'],receipt=receipt,receipt_sha256=sha(data))
        for suffix in ['stdout','stderr']:
            output=(state/(stem+'.'+suffix)).read_bytes()
            if sha(output)!=receipt[suffix+'_sha256']:raise ValueError('compiler output differs')
            row[suffix]=dict(bytes=len(output),sha256=sha(output),content_utf8=output.decode('utf-8'))
        rows.append(row)
    interrupted=[]
    prebatch_path=batch/'PRE-BATCH-STATE.json'
    prebatch=json.loads(prebatch_path.read_text()) if prebatch_path.exists() else None
    if terminal['exit_code'] or terminal['stop']:
        plan=json.loads((state/'PLAN.json').read_text())['modules']
        after=inventory(state)
        changed=[name for name,digest in after.items() if prebatch is None or prebatch.get(name)!=digest]
        represented={f"{row['index']:04d}" for row in rows}
        for stem in sorted({Path(name).stem for name in changed}-represented):
            index=int(stem)
            if index>=len(plan):raise ValueError('interrupted log has no selected module')
            record=dict(index=index,selected_module=plan[index],
                        status='EVENTLESS_UNVERIFIED_EVIDENCE',
                        attribution=('changed_since_prebatch' if prebatch is not None
                                     else 'prebatch_inventory_unavailable_may_include_older_files'),outputs={})
            for suffix in ['json','stdout','stderr']:
                path=state/(stem+'.'+suffix)
                if path.exists():
                    data=path.read_bytes()
                    record['outputs'][suffix]=dict(bytes=len(data),sha256=sha(data),
                                                  exact_bytes_base64=base64.b64encode(data).decode(),
                                                  content_utf8=data.decode('utf-8',errors='replace'))
            interrupted.append(record)
    else:
        summaries=[]
        for line in (batch/'stdout').read_text().splitlines():
            try:entry=json.loads(line)
            except json.JSONDecodeError:continue
            if isinstance(entry,dict) and entry.get('status')=='BATCH_COMPLETE':summaries.append(entry)
        if len(summaries)!=1 or summaries[0]['freshly_compiled']!=len(events):
            raise ValueError('successful batch summary differs from captured invocations')
    result=dict(schema='astra_exact_external_batch_v2',capture_runner_sha256=LOADED_SHA,
                guard_receipt_sha256=sha((batch/'RECEIPT.json').read_bytes()),
                guard_exit_code=terminal['exit_code'],guard_stop=terminal['stop'],
                prebatch_inventory_sha256=sha(prebatch_path.read_bytes()) if prebatch is not None else None,
                completed_compiler_invocations=rows,interrupted_unverified_invocations=interrupted,
                binaries_included=False,
                previous916_receipts='../2026-10-13-astra-unified-solver-0645z/evidence/MATHLIB-SOURCE-EXECUTION.json')
    output=batch/'MODULE-RECEIPTS.json'
    if check_existing:
        existing=json.loads(output.read_text())
        for key in ['guard_receipt_sha256','guard_exit_code','guard_stop',
                    'completed_compiler_invocations','binaries_included','previous916_receipts']:
            if existing[key]!=result[key]:raise ValueError('existing capture differs: '+key)
        if existing.get('interrupted_unverified_invocations',[])!=interrupted:
            raise ValueError('existing capture omits interrupted invocations')
        return dict(batch=batch.name,status='GUARD_OUTPUT_AND_COMPLETE_CAPTURE_REAUTHENTICATED',
                    records=len(rows),capture_sha256=sha(output.read_bytes()),
                    verifier_sha256=LOADED_SHA)
    with output.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    return dict(batch=batch.name,records=len(rows),bytes=output.stat().st_size,sha256=sha(output.read_bytes()))

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--state',type=Path,required=True);p.add_argument('--batch',type=Path,required=True)
    p.add_argument('--check-existing',action='store_true')
    a=p.parse_args();print(json.dumps(capture(a.state,a.batch,a.check_existing)))
