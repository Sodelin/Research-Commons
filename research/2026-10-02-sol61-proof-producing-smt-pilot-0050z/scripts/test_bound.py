#!/usr/bin/env python3
"""Final exact-source contract controls, preserving receipts."""
import pathlib,subprocess,json,time,resource
R=pathlib.Path(__file__).resolve().parents[1];out=[]
for name,inp,pf,expected in [('lra','lra','lra',0),('bool','bool','bool',0),('altered-input','lra-altered','lra',1),('corrupt-proof','lra','lra-corrupt',1),('trust-proof','lra','lra-trust',1)]:
 cmd=['python3',str(R/'scripts/check_bound.py'),str(R/f'inputs/{inp}.smt2'),str(R/f'proofs/{pf}.cpc')];t=time.monotonic();p=subprocess.run(cmd,capture_output=True,timeout=20)
 (R/f'receipts/final-{name}.stdout').write_bytes(p.stdout);(R/f'receipts/final-{name}.stderr').write_bytes(p.stderr)
 x=dict(name=name,command=cmd,exit_code=p.returncode,expected_exit_code=expected,elapsed_s=time.monotonic()-t,stdout=p.stdout.decode(),stderr=p.stderr.decode(),cumulative_child_max_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss);out.append(x);print(json.dumps(x))
 assert p.returncode==expected
(R/'receipts/final-contract-runs.json').write_text(json.dumps(out,indent=2))
