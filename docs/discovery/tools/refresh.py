#!/usr/bin/env python3
"""Fetch canonical PUBLIC authored claim source at one immutable main commit."""
import base64, hashlib, json, pathlib, subprocess
from datetime import datetime, timezone
ROOT = pathlib.Path(__file__).resolve().parents[1]
REPO = 'Sodelin/Research-Commons'
def api(path):
    return json.loads(subprocess.check_output(['gh','api','repos/'+REPO+path]))
if __name__ == '__main__':
    commit = api('/git/ref/heads/main')['object']['sha']
    source = api('/contents/docs/claims.json?ref='+commit)
    raw = base64.b64decode(source['content'])
    data = json.loads(raw)
    if not isinstance(data.get('claims'),list) or not data['claims']:
        raise ValueError('Refuse empty/malformed claim register')
    # Use the SAME browser/agent policy in RAM before persisting a source snapshot.
    subprocess.run(['node', str(ROOT/'tools/validate-source.mjs')], input=raw, capture_output=True, check=True)
    # Preserve the canonical author's source bytes, not a parallel registry.
    (ROOT/'dist/claims.json').write_bytes(raw)
    meta = {'repository':REPO,'commit':commit,'path':'docs/claims.json','git_blob':source['sha'],
            'sha256':hashlib.sha256(raw).hexdigest(),'board_version':data['board_version'],
            'source_updated_utc':data['updated_utc'],'retrieved_utc':datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
            'claim_count':len(data['claims']),'canonical_author':data['contributor']}
    (ROOT/'dist/source.json').write_text(json.dumps(meta,indent=2)+'\n')
    overlay = api('/contents/docs/subjective-reuse-ranking.json?ref='+commit)
    overlay_raw = base64.b64decode(overlay['content'])
    ranking = json.loads(overlay_raw)
    if ranking.get('subjective') is not True or not isinstance(ranking.get('entries'),list):
        raise ValueError('Refuse an unsupported subjective overlay')
    (ROOT/'dist/subjective-reuse-ranking.json').write_bytes(overlay_raw)
    (ROOT/'dist/ranking-source.json').write_text(json.dumps({'repository':REPO,'commit':commit,
        'path':'docs/subjective-reuse-ranking.json','git_blob':overlay['sha'],
        'sha256':hashlib.sha256(overlay_raw).hexdigest()},indent=2)+'\n')
    print(f"Canonical {len(data['claims'])}-claim source pinned at {commit}")
