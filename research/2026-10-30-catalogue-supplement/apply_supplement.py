"""Merge a pinned navigation supplement into a NEW corpus file, offline.

Usage: python apply_supplement.py BASE SUPPLEMENT OUTPUT
No network, installation, claim-status modification, or source overwrite.
"""
import hashlib
import json
import pathlib
import sys


def verify(doc):
    body = doc['body'].encode('utf-8')
    assert len(body) == doc['bytes'], 'byte count mismatch'
    assert hashlib.sha256(body).hexdigest() == doc['sha256'], 'SHA256 mismatch'
    blob = hashlib.sha1(b'blob ' + str(len(body)).encode() + b'\0' + body).hexdigest()
    assert blob == doc['git_blob'], 'Git blob mismatch'


def merge(base_bytes, supplement):
    assert hashlib.sha256(base_bytes).hexdigest() == supplement['base_corpus_sha256'], 'wrong base'
    base = json.loads(base_bytes)
    assert base['schema'] == supplement['schema'] == 1
    by_url = {}
    for doc in base['documents']:
        verify(doc)
        assert doc['url'] not in by_url, 'duplicate original URL'
        by_url[doc['url']] = doc
    original_count = len(by_url)
    for doc in supplement['documents']:
        verify(doc)
        assert doc['url'] not in by_url, 'duplicate supplement URL'
        assert '/blob/5672692b55e1cb0752c54fe631763cff7f14ce26/' in doc['url'], 'unexpected source pin'
        by_url[doc['url']] = doc
    base['documents'] = list(by_url.values())
    coverage = base['coverage']
    coverage['base_coverage_before_supplement'] = dict(coverage)
    coverage['indexed'] = len(by_url)
    coverage['selected_references'] += len(supplement['documents'])
    coverage['supplement_references'] = len(supplement['documents'])
    coverage['supplement_date_utc'] = supplement['date_utc']
    coverage['limitation'] += ' Three dated navigation sources added; registry and prior corpus metadata retain their historical pins. No claim status, archive completeness, deployed reader refresh, or proof acceptance follows.'
    return base, original_count


if __name__ == '__main__':
    source, supplement, destination = map(pathlib.Path, sys.argv[1:])
    result, original_count = merge(source.read_bytes(), json.loads(supplement.read_text()))
    with destination.open('x', encoding='utf-8') as out:
        json.dump(result, out, ensure_ascii=False, indent=2)
        out.write('\n')
    print(json.dumps({'original_verified': original_count, 'indexed': len(result['documents']), 'status': 'PASS'}))
