#!/usr/bin/env python3
"""Capture complete completed-batch compiler evidence without binary objects."""
import argparse
import hashlib
import json
from pathlib import Path


def sha(data):return hashlib.sha256(data).hexdigest()

def capture(state,batch):
    terminal=json.loads((batch/'RECEIPT.json').read_text())
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
    result=dict(schema='astra_exact_external_batch_v1',
                guard_receipt_sha256=sha((batch/'RECEIPT.json').read_bytes()),
                guard_exit_code=terminal['exit_code'],guard_stop=terminal['stop'],
                completed_compiler_invocations=rows,binaries_included=False,
                previous916_receipts='../2026-10-13-astra-unified-solver-0645z/evidence/MATHLIB-SOURCE-EXECUTION.json')
    output=batch/'MODULE-RECEIPTS.json'
    with output.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    return dict(batch=batch.name,records=len(rows),bytes=output.stat().st_size,sha256=sha(output.read_bytes()))

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--state',type=Path,required=True);p.add_argument('--batch',type=Path,required=True)
    a=p.parse_args();print(json.dumps(capture(a.state,a.batch)))
