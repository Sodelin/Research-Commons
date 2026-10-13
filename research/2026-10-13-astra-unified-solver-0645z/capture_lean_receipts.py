#!/usr/bin/env python3
"""Preserve complete compiler receipts and text output, never binary objects."""
import argparse
import base64
import hashlib
import json
from pathlib import Path


def artifact(path):
    data=path.read_bytes()
    row=dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
    try:
        row['content_utf8']=data.decode('utf-8')
    except UnicodeDecodeError:
        row['content_base64']=base64.b64encode(data).decode('ascii')
    return row


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--state',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    a=p.parse_args()
    plan=json.loads((a.state/'PLAN.json').read_text())
    rows=[]
    for index,source in enumerate(plan['modules']):
        stem=str(index).zfill(4)
        path=a.state/(stem+'.json')
        receipt=json.loads(path.read_text())
        if receipt['exit_code']!=0 or receipt['source_sha256']!=source['source_sha256']:
            raise ValueError('unfinished or mismatched source compilation: '+source['module'])
        row=dict(receipt=receipt,receipt_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
        for name in ['stdout','stderr']:
            row[name]=artifact(a.state/(stem+'.'+name))
            if row[name]['sha256']!=receipt[name+'_sha256']:
                raise ValueError('compiler output changed')
        rows.append(row)
    preserved={str(path.relative_to(a.state)):artifact(path) for folder in ['failures','interruptions']
               if (a.state/folder).exists() for path in (a.state/folder).rglob('*') if path.is_file()}
    plans={path.name:artifact(path) for path in a.state.glob('*PLAN.json')}
    result=dict(schema='astra_fresh_external_lean_execution_v1',plan=plan,
                exact_plan_artifacts=plans,compiled_modules=rows,preserved_failed_or_interrupted=preserved,
                binaries_included=False,
                status='ALL_SELECTED_EXTERNAL_SOURCES_HAVE_SUCCESSFUL_COMPILER_RECEIPTS',
                boundary='This captures completed execution evidence. Kernel build separately reauthenticates actual source/object bytes before reuse.')
    with a.out.open('x') as stream:
        json.dump(result,stream,indent=2)
        stream.write('\n')
    print(json.dumps(dict(status=result['status'],bytes=a.out.stat().st_size,
                          sha256=hashlib.sha256(a.out.read_bytes()).hexdigest())))


if __name__=='__main__':
    main()
