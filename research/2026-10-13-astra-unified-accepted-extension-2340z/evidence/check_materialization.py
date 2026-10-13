import hashlib
import json
from pathlib import Path
import runpy
import sys

packet = Path(__file__).resolve().parent.parent
pins = json.loads((packet / 'evidence/SOURCE-PINS.json').read_text())
for name, expected in pins.items():
    if hashlib.sha256((packet / name).read_bytes()).hexdigest() != expected:
        raise ValueError('source changed before execution: ' + name)
print(json.dumps(dict(executed_source_pins=pins,
    bootstrap_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())), flush=True)
sys.argv = [str(packet / 'materialize_extension.py'), '--out',
            '/workspace/scratch/astra-unified-extension-sources-2340']
runpy.run_path(str(packet / 'materialize_extension.py'), run_name='__main__')
