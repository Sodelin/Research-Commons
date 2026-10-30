#!/usr/bin/env python3
"""Verify exact published body identities in an all-result index, never fuzzy hit counts."""
import argparse,hashlib,json,pathlib,subprocess
p=argparse.ArgumentParser();p.add_argument('--repo',default='.');p.add_argument('--index',type=pathlib.Path,required=True);p.add_argument('--publication',action='append',required=True);a=p.parse_args();m=json.loads((a.index/'manifest.json').read_bytes());inventory={r['path']:r for r in m['inventory']};records=[]
def git(*args):return subprocess.check_output(['git','-C',a.repo,*args])
for ref in a.publication:
 commit=git('rev-parse',ref+'^{commit}').decode().strip();paths=git('diff-tree','--no-commit-id','--name-only','-r','-z',commit).split(b'\0');rows=[]
 for raw in paths:
  if not raw:continue
  path=raw.decode()
  if not any(path.startswith(root+'/') for root in m['roots']):continue
  entry=git('ls-tree','-z',commit,'--',path)
  if not entry:continue
  blob=entry.split()[2].decode();current=inventory.get(path)
  if not current:raise SystemExit('Published result missing from inventory: '+path)
  if current['git_blob']!=blob:
   rows.append({'path':path,'original_url':f'https://github.com/Sodelin/Research-Commons/blob/{commit}/{path}','coverage':'original_version_differs_from_current_tree','current_git_blob':current['git_blob'],'original_git_blob':blob});continue
  rows.append({'path':path,'original_url':f'https://github.com/Sodelin/Research-Commons/blob/{commit}/{path}','git_blob':blob,'coverage':current['coverage'],'body_sha256':current.get('sha256'),'reason':current.get('reason')})
 records.append({'publication_commit':commit,'artifacts':rows})
print(json.dumps({'index_commit':m['commit'],'publications':records,'limitation':'Exact version/body coverage, not scientific acceptance. Changed older versions are explicit gaps; private handoffs and unpublished extensions are excluded.'},indent=2))
