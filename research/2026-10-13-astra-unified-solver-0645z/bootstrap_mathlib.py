"""Serially compile the upstream cache utility, then fetch a narrow cache.

No research module compilation or cache trust beyond the pinned official
Mathlib source is implied. Use guard.py and new scratch for receipts.
Append --sources-only to prepare pinned dependencies without compiling the
cache utility or contacting its download service.
"""
from pathlib import Path
import json
import os
import re
import subprocess
import shlex
import sys

PIN = '0df444a360eaa60ab8c11dca51a86af692955474'


def main():
    mathlib, lean_bin, output = map(Path, sys.argv[1:4])
    if sys.argv[4:] not in ([], ['--sources-only']):
        raise ValueError('only optional flag is --sources-only')
    output.mkdir(parents=True, exist_ok=False)
    def call(cmd):
        subprocess.run(list(map(str,cmd)), cwd=mathlib, check=True)
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=mathlib,text=True).strip()==PIN
    os.environ['PATH'] = str(lean_bin)+os.pathsep+os.environ['PATH']
    # Reduce mimalloc virtual arena reservation to 16 MiB. This avoids startup
    # thread allocation failure under RLIMIT_AS without raising physical limits.
    os.environ['MIMALLOC_ARENA_RESERVE']='16384'
    os.environ['LEAN_NUM_THREADS']='1'
    os.environ['LEAN_STACK_SIZE_KB']='8192'
    os.environ['LEAN_IMPORT_WORKERS']='1'
    os.environ['MATHLIB_CACHE_DIR']=str(output/'cache')
    # Native Lake initialization exceeds the virtual-address budget on this
    # host even before compilation. Materialize precisely its pinned manifest
    # dependencies, then invoke the compiler directly, one module at a time.
    packages = mathlib / '.lake/packages'
    packages.mkdir(parents=True, exist_ok=True)
    deps = []
    for row in json.loads((mathlib/'lake-manifest.json').read_text())['packages']:
        path = packages / row['name']
        if not path.exists():
            call(['git', 'init', path])
            call(['git', '-C', path, 'remote', 'add', 'origin', row['url']])
            call(['git', '-C', path, 'fetch', '--depth=1', 'origin', row['rev']])
            call(['git', '-C', path, 'checkout', '--detach', 'FETCH_HEAD'])
        assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=path,text=True).strip()==row['rev']
        deps.append(path)
    if sys.argv[4:] == ['--sources-only']:
        (output/'PINNED-SOURCES.json').write_text(json.dumps(dict(mathlib_revision=PIN,
            dependencies=json.loads((mathlib/'lake-manifest.json').read_text())['packages'],
            compilation_performed=False, cache_download_attempted=False),indent=2)+'\n')
        print('Pinned source dependencies prepared; no compilation/cache download.')
        return
    os.environ['LEAN_PATH'] = os.pathsep.join(str(p/'.lake/build/lib/lean') for p in [mathlib,*deps])
    os.environ['LEAN_SRC_PATH'] = os.pathsep.join(map(str,[mathlib,*deps,lean_bin.parent/'src/lean']))
    os.environ['RAYON_NUM_THREADS'] = '1'
    # Cache.IO queries `lean --print-prefix`; ensure that subprocess also uses
    # the explicit serial frontend. No official binary is changed.
    wrapper = output/'bin'
    wrapper.mkdir()
    (wrapper/'lean').write_text('#!/bin/sh\nexec '+shlex.quote(str(lean_bin/'lean'))+' -j 1 -s 8192 "$@"\n')
    (wrapper/'lean').chmod(0o700)
    os.environ['PATH'] = str(wrapper)+os.pathsep+os.environ['PATH']
    call([lean_bin/'lean','-j','1','-s','8192','--version'])
    build=mathlib/'.lake/build/lib/lean'
    selected={}
    def visit(name):
        if name in selected:
            return
        if name.startswith('Cache.'):
            source=mathlib/(name.replace('.','/')+'.lean')
            target=build/(name.replace('.','/')+'.olean')
        elif name=='Batteries.Tactic.OpenPrivate':
            package=mathlib/'.lake/packages/batteries'
            source=package/(name.replace('.','/')+'.lean')
            target=package/'.lake/build/lib/lean'/(name.replace('.','/')+'.olean')
        else:
            return
        for dep in re.findall(r'^import\s+([\w.]+)',source.read_text(),re.M):
            visit(dep)
        target.parent.mkdir(parents=True,exist_ok=True)
        call([lean_bin/'lean','-j','1','-s','8192','-t','0','-o',target,source])
        selected[name]=str(source)
    for name in ['Cache.Cli','Cache.Requests','Cache.Marker','Cache.Query','Cache.Warning']:
        visit(name)
    (output/'SERIAL-CACHE-COMPILATION.json').write_text(json.dumps(selected,indent=2)+'\n')
    call([lean_bin/'lean','-j','1','-s','8192','--run','Cache/Main.lean','get',
          'Mathlib.Data.Real.Basic','Mathlib.Algebra.BigOperators.Group.Finset.Basic',
          'Mathlib.Tactic.Ring','Mathlib.Tactic.Linarith','Mathlib.Tactic.Positivity'])


if __name__=='__main__':
    main()
