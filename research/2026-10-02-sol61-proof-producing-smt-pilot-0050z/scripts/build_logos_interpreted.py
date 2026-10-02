#!/usr/bin/env python3
"""Bounded sequential official-source Logos build, no native compiler."""
import pathlib, subprocess, os, time, json, resource
R=pathlib.Path(__file__).resolve().parents[1]
SRC=R/'vendor/logos-49f4fd1f256f5504f1a21c61c1808ffc56eeb6b8'
OUT=R/'logos-lean'; OUT.mkdir(exist_ok=True)
LEAN='/workspace/shared/lean-formalization/tooling/lean-4.33.1-linux/bin/lean'
env=dict(os.environ,LEAN_PATH=str(OUT))
order=json.loads((R/'receipts/logos-executable-module-order.json').read_text())
start=time.monotonic(); receipts=[]; status='complete'
for mod,size in order:
 path=pathlib.Path(mod.replace('.','/')+'.lean'); out=OUT/path.with_suffix('.olean'); out.parent.mkdir(parents=True,exist_ok=True)
 cmd=[LEAN,'-j1','-M2048','-DmaxHeartbeats=10000000','-DwarningAsError=true','-o',str(out),str(path)]
 t=time.monotonic(); remaining=60-(t-start)
 if remaining<=0: status='bounded_timeout'; break
 try:
  p=subprocess.run(cmd,cwd=SRC,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=remaining)
  rc=p.returncode; stdout=p.stdout; stderr=p.stderr
 except subprocess.TimeoutExpired as e:
  rc=124; stdout=e.stdout or b''; stderr=e.stderr or b''; status='bounded_timeout'
 stem=mod.replace('.','_'); (R/'receipts'/f'{stem}.stdout').write_bytes(stdout); (R/'receipts'/f'{stem}.stderr').write_bytes(stderr)
 receipts.append(dict(module=mod,source_bytes=size,command=cmd,exit_code=rc,elapsed_s=time.monotonic()-t,object_exists=out.exists(),cumulative_child_max_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss))
 print(json.dumps(receipts[-1]),flush=True)
 if rc!=0: status='bounded_timeout' if rc==124 else 'failed'; break
res=dict(status=status,elapsed_s=time.monotonic()-start,runtime=LEAN,upstream_toolchain='leanprover/lean4:v4.33.0',tested_toolchain='Lean4.33.1',sequential=True,timeout_s=60,lean_memory_cap_mib=2048,modules=receipts)
(R/'receipts/logos-interpreted-build.json').write_text(json.dumps(res,indent=2)); print(json.dumps(res),flush=True)
