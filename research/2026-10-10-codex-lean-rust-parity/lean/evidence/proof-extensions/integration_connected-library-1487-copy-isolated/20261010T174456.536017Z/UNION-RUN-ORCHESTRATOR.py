#!/usr/bin/env python3
# Codex / lean_integration_successor, 2026-10-10. Serial unchanged strict union,
# read-only complete cache transport rehash, then lossless evidence preservation.
import os,subprocess,pathlib,json,shutil
W=pathlib.Path('/tmp/rc-lean-integrated-library-union-1487-20261010T174456.536017Z')
env=dict(os.environ,CONNECTED_LEAN_BIN='/workspace/toolchains/lean-4.33.1-linux/bin',CONNECTED_MATHLIB='/workspace/dependencies/mathlib4')
r=subprocess.run(['python3','scripts/run_proof_extensions.py',str(W)],env=env)
post_code=None
try:
    if r.returncode==0:
        run=pathlib.Path(json.loads((W/'.build/LATEST-RUN.json').read_bytes())['run'])
        post=subprocess.run(['python3','scripts/verify_cache_transport_after_run.py',str(W)],capture_output=True,text=True)
        post_code=post.returncode
        (run/'CACHE-TRANSPORT-POST-VERIFIER.stdout').write_text(post.stdout)
        (run/'CACHE-TRANSPORT-POST-VERIFIER.stderr').write_text(post.stderr)
        print(post.stdout,flush=True)
        if post.stderr: print(post.stderr,flush=True)
        shutil.copyfile('scripts/verify_cache_transport_after_run.py',run/'CACHE-TRANSPORT-POST-VERIFIER.py')
        if post_code==0: shutil.copyfile(W/'CACHE-TRANSPORT-POST-RUN-REHASH.json',run/'CACHE-TRANSPORT-POST-RUN-REHASH.json')
finally:
    subprocess.run(['python3','scripts/preserve_recovery_result.py',str(W),'--result-file','INTEGRATED-MODULAR-UNION-RESULT.json'],check=True)
if r.returncode==0 and post_code==0:
    subprocess.run(['python3','scripts/summarize_proof_extension.py','INTEGRATED-MODULAR-UNION-RESULT.json','--certificate','INTEGRATED-MODULAR-UNION-CERTIFICATE.json'],check=True)
raise SystemExit(r.returncode or post_code or 0)
