#!/usr/bin/env python3
"""Fetch canonical PUBLIC authored claim source at one immutable main commit."""
import argparse, base64, hashlib, json, pathlib, re, subprocess
from datetime import datetime, timezone
ROOT = pathlib.Path(__file__).resolve().parents[1]
REPO = 'Sodelin/Research-Commons'
def api(path):
    return json.loads(subprocess.check_output(['gh','api','repos/'+REPO+path]))
def persist_snapshot(commit, source, overlay, expected_sha256=None):
    raw = base64.b64decode(source['content'])
    overlay_raw = base64.b64decode(overlay['content'])
    if expected_sha256 is not None and hashlib.sha256(raw).hexdigest()!=expected_sha256:
        raise ValueError('Reviewed source hash mismatch; no snapshot was persisted')
    data = json.loads(raw)
    # Both deliberately public source bodies stay in RAM until shared validation.
    validator = str(ROOT/'tools/validate-source.mjs')
    subprocess.run(['node', validator], input=raw, capture_output=True, check=True)
    subprocess.run(['node', validator, '--ranking'], input=overlay_raw, capture_output=True, check=True)
    meta = {'repository':REPO,'commit':commit,'path':'docs/claims.json','git_blob':source['sha'],
            'sha256':hashlib.sha256(raw).hexdigest(),'board_version':data['board_version'],
            'source_updated_utc':data['updated_utc'],'retrieved_utc':datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
            'claim_count':len(data['claims']),'canonical_author':data['contributor']}
    # Preserve exact authored bytes; validation failure reaches no write method.
    (ROOT/'dist/claims.json').write_bytes(raw)
    (ROOT/'dist/source.json').write_text(json.dumps(meta,indent=2)+'\n')
    (ROOT/'dist/subjective-reuse-ranking.json').write_bytes(overlay_raw)
    (ROOT/'dist/ranking-source.json').write_text(json.dumps({'repository':REPO,'commit':commit,
        'path':'docs/subjective-reuse-ranking.json','git_blob':overlay['sha'],
        'sha256':hashlib.sha256(overlay_raw).hexdigest()},indent=2)+'\n')
    return len(data['claims'])

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--commit', help='Exact reviewed public source commit; otherwise current main')
    parser.add_argument('--expected-sha256', help='Require the reviewed canonical claim body hash before writing')
    args = parser.parse_args()
    if args.commit and not re.fullmatch('[0-9a-f]{40}',args.commit):
        parser.error('--commit requires an exact lower-case Git commit identity')
    if args.expected_sha256 and not re.fullmatch('[0-9a-f]{64}',args.expected_sha256):
        parser.error('--expected-sha256 requires an exact lower-case SHA256 identity')
    commit = args.commit or api('/git/ref/heads/main')['object']['sha']
    source = api('/contents/docs/claims.json?ref='+commit)
    overlay = api('/contents/docs/subjective-reuse-ranking.json?ref='+commit)
    count = persist_snapshot(commit, source, overlay,args.expected_sha256)
    print(f"Canonical {count}-claim source pinned at {commit}")
