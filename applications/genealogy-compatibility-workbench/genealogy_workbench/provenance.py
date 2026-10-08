"""Content-bound receipts. Hash binding is not a formal proof or authentication."""
from hashlib import sha256
from pathlib import Path
import json
import platform
from .core import InputError

ROOT=Path(__file__).resolve().parent

def canonical(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()

def digest(value):return sha256(canonical(value)).hexdigest()

def engine_files():
    paths=sorted(ROOT.rglob('*.py'))+[ROOT/'provenance-registry.json']
    return {str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest() for p in paths}

def registry():return json.loads((ROOT/'provenance-registry.json').read_text())

def verify_vendor():
    for entry in registry()['reused_source_artifacts']:
        path=ROOT/entry['vendored_path']
        if sha256(path.read_bytes()).hexdigest()!=entry['sha256']:
            raise InputError(f'Changed source/proof binding: {entry["vendored_path"]}')

def receipt(operation,input_data,result):
    verify_vendor()
    body={'schema':'genealogy-workbench/receipt-v1','operation':operation,'input_sha256':digest(input_data),
        'engine_files_sha256':engine_files(),'python_version':platform.python_version(),
        'scientific_registry':registry(),'result':result,'lean_kernel_checked':False,
        'binding_scope':'Reproducibility/integrity check against this input and current code; not a signature, proof-assistant verification or biological validation'}
    return {**body,'receipt_sha256':digest(body)}

def verify_receipt(input_data,saved,runner):
    verify_vendor()
    if not isinstance(saved,dict):
        raise InputError('Receipt must be a JSON object')
    body={k:v for k,v in saved.items() if k!='receipt_sha256'}
    if saved.get('schema')!='genealogy-workbench/receipt-v1' or saved.get('receipt_sha256')!=digest(body):
        raise InputError('Receipt contents/hash changed')
    if saved.get('input_sha256')!=digest(input_data):raise InputError('Changed input binding')
    if saved.get('engine_files_sha256')!=engine_files():raise InputError('Changed engine/provenance binding')
    rebuilt=runner(saved['operation'],input_data)
    if canonical(rebuilt)!=canonical(saved['result']):raise InputError('Receipt result does not reproduce')
    return {'status':'PASS','input_binding':'PASS','engine_binding':'PASS','result_reexecution':'PASS','lean_kernel_checked':False}
