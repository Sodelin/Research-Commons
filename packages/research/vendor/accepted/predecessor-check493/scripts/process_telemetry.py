"""Read-only /proc sampling of the launched build's actual Lean descendants."""
from pathlib import Path
import json,os,time,datetime
FIELDS=('VmRSS','VmHWM','VmSize','VmPeak')
def parse_stat(raw):
 end=raw.rfind(')');start=raw.find('(');tail=raw[end+2:].split()
 return {'pid':int(raw[:start].strip()),'comm':raw[start+1:end],'ppid':int(tail[1]),'start_ticks':int(tail[19])}
def parse_status(raw):
 out={}
 for line in raw.splitlines():
  key,sep,value=line.partition(':')
  if sep and key in FIELDS:
   bits=value.split();out[key+'_bytes']=int(bits[0])*1024
 return out
def descendants(rows,root):
 result={root}
 while True:
  new={p for p,d in rows.items() if d['ppid'] in result}
  if new<=result:return result
  result|=new
def available_ram():
 return int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024
class Sampler:
 def __init__(self,out,interval=0.1):
  self.out=Path(out);self.stream=self.out.open('x');self.interval=interval;self.records={};self.samples=0;self.races=0;self.errors=[];self.min_ram=None
 def observe(self,root):
  try:self._observe(root)
  except Exception as ex:self.errors.append({'monotonic':time.monotonic(),'error':repr(ex)})
 def _observe(self,root):
  rows={}
  for p in Path('/proc').iterdir():
   if not p.name.isdecimal():continue
   try:rows[int(p.name)]=parse_stat((p/'stat').read_text())
   except (OSError,ValueError,IndexError):self.races+=1
  ram=available_ram();self.min_ram=ram if self.min_ram is None else min(self.min_ram,ram)
  for pid in descendants(rows,root):
   d=rows.get(pid)
   if not d or d['comm']!='lean':continue
   p=Path('/proc')/str(pid)
   try:
    metrics=parse_status((p/'status').read_text());argv=(p/'cmdline').read_bytes().decode(errors='replace').rstrip('\0').split('\0');cwd=os.readlink(p/'cwd');exe=os.readlink(p/'exe');check=parse_stat((p/'stat').read_text())
    if check['start_ticks']!=d['start_ticks']:self.races+=1;continue
   except (OSError,ValueError,IndexError):self.races+=1;continue
   if not all(k+'_bytes' in metrics for k in FIELDS):self.races+=1;continue
   key=str(pid)+':'+str(d['start_ticks']);now=time.monotonic();row={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'monotonic':now,'process_key':key,'pid':pid,'start_ticks':d['start_ticks'],'argv':argv,'cwd':cwd,'executable':exe,'available_ram_bytes':ram,**metrics};self.stream.write(json.dumps(row)+'\n');self.stream.flush();self.samples+=1
   rec=self.records.setdefault(key,{'pid':pid,'start_ticks':d['start_ticks'],'argv':argv,'cwd':cwd,'executable':exe,'first_sample_monotonic':now,'samples':0})
   rec['samples']+=1;rec['last_sample_monotonic']=now
   for k,v in metrics.items():rec['maximum_observed_'+k]=max(rec.get('maximum_observed_'+k,0),v)
 def finish(self,path):
  self.stream.close();result={'status':'OBSERVATIONS_RECORDED' if self.samples and not self.errors else 'INCOMPLETE_TELEMETRY','interval_seconds':self.interval,'samples':self.samples,'processes':self.records,'process_read_races':self.races,'unexpected_errors':self.errors,'minimum_observed_available_ram_bytes':self.min_ram,'semantics':'Per-process /proc observations of actual Lean descendants keyed by PID and start ticks. VmHWM/VmPeak are sampled kernel high-water values; no claim of observing an exited process final maximum. VmSize/VmPeak are virtual address space, not physical RAM. This sampler does not change compiler commands, kernel checks, memory/time limits or supervisor decisions.'};Path(path).write_text(json.dumps(result,indent=2)+'\n');return result
