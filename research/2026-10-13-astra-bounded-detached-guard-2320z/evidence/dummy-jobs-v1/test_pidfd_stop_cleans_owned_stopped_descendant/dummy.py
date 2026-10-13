import subprocess,sys,os,signal,time,json
from pathlib import Path
p=subprocess.Popen([sys.executable,"-c","import time;time.sleep(20)"])
os.kill(p.pid,signal.SIGSTOP)
Path("descendant.json").write_text(json.dumps({"pid":p.pid}))
time.sleep(20)
