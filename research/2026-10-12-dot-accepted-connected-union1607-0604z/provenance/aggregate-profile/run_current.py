"""Scheduling-only Lake adapter. All compiler/audit/storage rules are inherited."""
from pathlib import Path
import os,subprocess,sys
root=Path(__file__).resolve().parents[1]
cmd=[sys.executable,str(root/'scripts/run_aggregate1607.py'),'--lean-bin',os.environ['CONNECTED_LEAN_BIN'],'--mathlib',os.environ['CONNECTED_MATHLIB'],'--backing-store',str(root),'--target',sys.argv[1] if len(sys.argv)>1 else 'current/connected']
raise SystemExit(subprocess.call(cmd,cwd=root))
