#!/usr/bin/env python3
import json,time
from pathlib import Path
root=Path(__file__).resolve().parents[1]
last=json.loads((root/'.build/LATEST-RUN.json').read_bytes())
run=Path(last['run']);events=[json.loads(x) for x in (run/'EVENTS.jsonl').read_text().splitlines() if x]
attempts=sorted((run/'attempts').glob('*')) if (run/'attempts').exists() else []
print(json.dumps({'status':last['status'],'run':run.name,'fresh_component_passes':sum(e.get('status')=='FRESH_KERNEL_PASS' for e in events),'last_event':events[-1] if events else None,'current_attempt':attempts[-1].name if attempts else None,'active_attempt_receipt_exists':(attempts[-1]/'receipt.json').exists() if attempts else None,'observed_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}))
