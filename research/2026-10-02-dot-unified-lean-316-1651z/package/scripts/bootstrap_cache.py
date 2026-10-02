#!/usr/bin/env python3
"""Create writable metadata over a pinned, read-only existing Lean cache.

Source/artifact bytes are borrowed read-only; mutable .hash/.trace/config
metadata belongs to this workspace. No update/download hook is invoked.
"""
from pathlib import Path
import json, os, shutil
ROOT=Path(__file__).resolve().parents[1]
if not os.environ.get('UNIFIED_MATHLIB_CACHE'):
  raise RuntimeError('Set UNIFIED_MATHLIB_CACHE to the matching built mathlib checkout')
OLD=Path(os.environ['UNIFIED_MATHLIB_CACHE']).expanduser().resolve()
DEST=ROOT/'deps/mathlib';DEST.mkdir(parents=True,exist_ok=True)

def mirror(src,dst,skip_packages=False):
  for current,dirs,files in os.walk(src):
    rel=Path(current).relative_to(src);out=dst/rel;out.mkdir(parents=True,exist_ok=True)
    if '.git' in dirs:
      q=out/'.git'
      if not q.exists():q.symlink_to((Path(current)/'.git').resolve(),target_is_directory=True)
      dirs.remove('.git')
    if skip_packages and rel==Path('.lake') and 'packages' in dirs:dirs.remove('packages')
    for f in files:
      source=Path(current)/f;target=out/f
      if target.exists() or target.is_symlink():continue
      mutable=(f.endswith(('.hash','.trace','.json')) or '.lake/config' in str(rel) or f in {'lakefile.lean','lakefile.toml','lean-toolchain'})
      if mutable:shutil.copy2(source,target)
      else:target.symlink_to(source.resolve())

mirror(OLD,DEST,True)
packages=ROOT/'.lake/packages';packages.mkdir(parents=True,exist_ok=True)
archive=ROOT/'.lake/borrowed-package-links';archive.mkdir(parents=True,exist_ok=True)
for p in sorted((OLD/'.lake/packages').iterdir()):
  if not p.is_dir():continue
  q=packages/p.name
  if q.is_symlink():q.rename(archive/p.name)
  q.mkdir(parents=True,exist_ok=True);mirror(p,q)
pd=DEST/'.lake/packages';pd.mkdir(parents=True,exist_ok=True)
for p in packages.iterdir():
  q=pd/p.name
  if p.is_dir() and not q.exists():q.symlink_to(p.resolve(),target_is_directory=True)
manifest=json.loads((ROOT/'lake-manifest.json').read_text())
entry=next(p for p in manifest['packages'] if p['name']=='mathlib')
entry['dir']='deps/mathlib'
(ROOT/'lake-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert 'deps/mathlib' in (ROOT/'lakefile.lean').read_text(), 'Relative dependency layout required'
print(json.dumps({'mathlib_source_cache':str(OLD),'metadata_overlay':str(DEST),
 'package_names':sorted(p.name for p in packages.iterdir()),'upstream_sources_mutated':False}))
