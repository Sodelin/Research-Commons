#!/usr/bin/env python3
"""Build only pinned official Ethos checker; same source/flags as CMake, O0."""
import pathlib,subprocess,time,resource,json,os,signal
R=pathlib.Path(__file__).resolve().parents[1]; SRC=R/'vendor/ethos-08e4aa40c4f8a6e00833f10e8d8985777e424027'; OUT=R/'ethos'; sources=sorted(SRC.glob('src/**/*.cpp'))
cmd=['g++','-Wall','-Wno-deprecated','-std=gnu++17','-O0','-I'+str(SRC/'src'),*[str(p) for p in sources],'-lgmp','-o',str(OUT)]
t=time.monotonic()
def limit():
 resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
 os.setsid()
p=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,preexec_fn=limit)
try:stdout,stderr=p.communicate(timeout=60); rc=p.returncode
except subprocess.TimeoutExpired:
 os.killpg(p.pid,signal.SIGKILL); stdout,stderr=p.communicate();rc=124
(R/'receipts/ethos-build.stdout').write_bytes(stdout);(R/'receipts/ethos-build.stderr').write_bytes(stderr)
r=dict(command=cmd,exit_code=rc,elapsed_s=time.monotonic()-t,cumulative_child_max_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,memory_cap_bytes=2*1024**3,timeout_s=60,executable_exists=OUT.exists(),upstream_commit='08e4aa40c4f8a6e00833f10e8d8985777e424027',build_note='CMake3.12+ not installed; src/CMakeLists.txt merely globs source cpp and links GMP. Direct equivalent C++17 build, O0 instead of release optimization, no plugins.')
(R/'receipts/ethos-build.json').write_text(json.dumps(r,indent=2));print(json.dumps(r),flush=True)
