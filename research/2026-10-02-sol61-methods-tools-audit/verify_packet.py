"""Hash verification only: no research jobs, network, or compilation."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
for manifest_name in ('publication-manifest.json','manifest.json'):
    data=json.loads((root/manifest_name).read_text())
    for row in data['files']:
        p=root/row['file']
        if not p.exists() and manifest_name=='manifest.json' and row['file']=='SyntheticCertificate.olean':
            print('OMITTED generated object; historical source hash and replay instructions preserved:',row['file'],row['sha256'])
            continue
        b=p.read_bytes()
        assert len(b)==row['bytes'] and hashlib.sha256(b).hexdigest()==row['sha256'],row['file']
print('PASS: all published files match their recorded hashes; historical binary omission is explicit')
