#!/usr/bin/env python3
import pathlib, subprocess, resource, time, json, re, os, signal, hashlib
R=pathlib.Path(__file__).resolve().parents[1]; CVC=R/'vendor/cvc5-Linux-x86_64-static/bin/cvc5'; ETHOS=R/'ethos'; SIG=R/'vendor/cvc5-cvc5-1.4.1/proofs/eo/cpc/Cpc.eo'
receipts=[]
def run(name,cmd):
 t=time.monotonic()
 def limit():
  resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));os.setsid()
 p=subprocess.Popen([str(x) for x in cmd],stdout=subprocess.PIPE,stderr=subprocess.PIPE,preexec_fn=limit)
 try:stdout,stderr=p.communicate(timeout=20);rc=p.returncode
 except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);stdout,stderr=p.communicate();rc=124
 (R/'receipts'/f'{name}.stdout').write_bytes(stdout);(R/'receipts'/f'{name}.stderr').write_bytes(stderr)
 r=dict(name=name,command=[str(x) for x in cmd],exit_code=rc,elapsed_s=time.monotonic()-t,cumulative_child_max_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,stdout=stdout.decode(errors='replace'),stderr=stderr.decode(errors='replace'),timeout_s=20,memory_cap_bytes=2*1024**3)
 receipts.append(r);(R/'receipts/pilot-runs.json').write_text(json.dumps(receipts,indent=2));print(json.dumps(r),flush=True);return r
for name in ['lra','bool']:
 result=run(name+'-solver',[CVC,'--safe-mode=safe','--dump-proofs',R/f'inputs/{name}.smt2'])
 if result['exit_code']!=0:continue
 lines=result['stdout'].splitlines()
 if not (lines[0]=='unsat' and lines[1]=='(' and lines[-1]==')'):raise ValueError('unexpected certificate framing')
 (R/f'proofs/{name}.cpc').write_text('\n'.join(lines[2:-1])+'\n')
check=[ETHOS,'--include='+str(SIG),'--require-proof-of-false','--normalize-num']
run('ethos-config',[ETHOS,'--show-config'])
run('lra-check-unbound',[*check,R/'proofs/lra.cpc'])
run('lra-check-bound',[*check,'--reference='+str(R/'inputs/lra.smt2'),R/'proofs/lra.cpc'])
run('lra-corrupt-check',[*check,'--reference='+str(R/'inputs/lra.smt2'),R/'proofs/lra-corrupt.cpc'])
run('lra-altered-input-check',[*check,'--reference='+str(R/'inputs/lra-altered.smt2'),R/'proofs/lra.cpc'])
run('lra-altered-solver',[CVC,'--safe-mode=safe',R/'inputs/lra-altered.smt2'])
run('bool-check-bound',[*check,'--reference='+str(R/'inputs/bool.smt2'),R/'proofs/bool.cpc'])
