"""Install hash-pinned G2 providers from the actual successful timed closure.

The import visitor still selects only dependencies of requested targets.
Original source/provider files and baseline Lake registrations are unchanged.
"""
import hashlib
import json
from pathlib import Path
import shutil
import sys

repo, build = map(Path, sys.argv[1:3])
manifest_path = repo / ('research/2026-10-07-cloud-g5-sol-ultra-1557z/verification/evidence/'
    'g5-takeover-run-37658528073-PASS/SOURCE-CONTEXT.json')
assert hashlib.sha256(manifest_path.read_bytes()).hexdigest() == \
    'e165eab8a20daddbd1f59160b9edc0de93181d85c2a55b485803f586f04a209e'
manifest = json.loads(manifest_path.read_text())
assert manifest['source_commit'] == '849757a968ea29e215c569b16bf3ca6d15af6abc'
installed = {}
for module, record in manifest['modules'].items():
    if not module.startswith('G2'):
        continue
    source = repo / record['source']
    assert hashlib.sha256(source.read_bytes()).hexdigest() == record['sha256'], module
    destination = build / (module + '.lean')
    shutil.copyfile(source, destination)
    installed[module] = {'source': record['source'], 'sha256': record['sha256']}
print('G6_TIMED_G2_PROVIDERS ' + json.dumps(installed), flush=True)
