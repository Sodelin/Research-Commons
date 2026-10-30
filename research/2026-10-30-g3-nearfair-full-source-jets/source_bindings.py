import hashlib,json,math
from pathlib import Path

def verify(root):
    m=json.loads(Path(__file__).with_name('SOURCE-BINDINGS.json').read_text())
    for item in m['inputs']:
        if hashlib.sha256((root/item['path']).read_bytes()).hexdigest()!=item['sha256']:
            raise SystemExit('SOURCE HASH MISMATCH: '+item['path'])
    p=10007
    assert all(p%d for d in range(2,math.isqrt(p)+1))
