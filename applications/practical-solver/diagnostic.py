"""Bounded, separately executed complete-cover pair diagnostic; cannot alter cover."""
import argparse
import hashlib
import json
from pathlib import Path
import sys
from types import ModuleType

APP=Path(__file__).resolve().parent
INHERITED=APP.parents[1]/'research/2026-10-08-codex-integration-0825z/practical'
SHA='0ee32b5d0a72fb1fbe426cde97dd018d009e4b8dee0e63e057d6e3d9cb93598c'

def main():
 p=argparse.ArgumentParser();p.add_argument('--request',type=Path,required=True);p.add_argument('--checker',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--native-binary',type=Path);a=p.parse_args()
 a.output.mkdir(exist_ok=False);request=json.loads(a.request.read_bytes());checked=json.loads(a.checker.read_bytes());root=INHERITED/'recovered'
 path=root/'research/2026-10-08-cloud-rust-signed-probe-0122z/compare_signed.py';raw=path.read_bytes()
 if path.is_symlink() or hashlib.sha256(raw).hexdigest()!=SHA:raise ValueError('Captured comparator identity mismatch')
 mod=ModuleType('_authenticated_comparator');mod.__file__=str(path);sys.modules[mod.__name__]=mod;exec(compile(raw,str(path),'exec',dont_inherit=True),mod.__dict__)
 manifest=json.loads((path.parent/'FROZEN-SOURCES.json').read_bytes());before=mod.source_state(root,manifest);reference=mod.load_reference(root)
 cover=checked.get('physical_cover',[]);result={'status':'REFERENCE_DIAGNOSTIC','description':'authenticated Python post-checker pair diagnostic; native binary absent',
 'changes_checked_cover':False,'source_feasibility_certified':False,'statistical_coverage_verified':False,'parameter_accuracy_released':False,
 'executed_comparator_sha256':SHA,'native_called':False}
 if not checked.get('details',{}).get('complete_numeric_replay') or not 0<len(cover)<=8:
  result.update(status='DIAGNOSTIC_REFUSED',reason='complete nonempty replayed cover with at most eight cells required')
 else:
  cases=[{'id':f'pair_{i}_{j}','means0':request['features'],'means1':request['features'],'physical0':left['box'],'physical1':right['box'],
    'precision':96,'max_bits':4096,'max_exp_calls':24} for i,left in enumerate(cover) for j,right in enumerate(cover)]
  expected=[reference.receive(root,c['means0'],c['means1'],c['physical0'],c['physical1'],c['precision'],c['max_bits'],c['max_exp_calls']) for c in cases]
  result.update(all_complete_cover_cells_consumed=len(cover),ordered_pairs=len(cases),cases=cases,python_expected=expected)
  if a.native_binary:
   binary=a.native_binary.absolute()
   if binary.is_symlink() or not binary.is_file() or binary.stat().st_size>32*2**20:raise ValueError('Native binary must be a regular bounded file')
   binary_hash=hashlib.sha256(binary.read_bytes()).hexdigest();lines=mod.run_native(binary,('\n'.join(mod.row(c) for c in cases)+'\n').encode('ascii'),a.output,'native-pairs')
   actual=[mod.parse_native(line,c) for line,c in zip(lines,cases)]
   matches=len(lines)==len(cases) and all(x==mod.project_reference(y) for x,y in zip(actual,expected))
   unchanged=hashlib.sha256(binary.read_bytes()).hexdigest()==binary_hash
   result.update(status='COMPATIBILITY_PASS' if matches and unchanged else 'DIAGNOSTIC_MISMATCH',native_called=True,native_actual=actual,
     binary_sha256=binary_hash,exact_fields_match=matches,binary_unchanged=unchanged,description='native versus authenticated Python post-checker pair diagnostic; no producer replacement or acceleration')
 result['authenticated_sources_unchanged']=before==mod.source_state(root,manifest)
 if not result['authenticated_sources_unchanged']:
  result.update(status='DIAGNOSTIC_SOURCE_CHANGED',description='diagnostic source identity changed; complete checked cover unchanged')
 (a.output/'RESULT.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':result['status'],'ordered_pairs':result.get('ordered_pairs')},sort_keys=True))
if __name__=='__main__':main()
