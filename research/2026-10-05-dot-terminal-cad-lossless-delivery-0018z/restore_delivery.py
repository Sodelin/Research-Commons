#!/usr/bin/env python3
"""Restore one lossless research receipt and verify the complete original inventory."""
import argparse, gzip, hashlib, json, os, pathlib, tempfile

def check_bytes(data, row):
    if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
        raise ValueError('size/SHA-256 mismatch')
    if hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() != row['git_blob_sha1']:
        raise ValueError('Git blob mismatch')

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=pathlib.Path,default=pathlib.Path(__file__).resolve().parents[2])
    p.add_argument('--verify-only',action='store_true',help='decode and verify without writing')
    args=p.parse_args(); root=args.root.resolve()
    ledger=json.loads((pathlib.Path(__file__).parent/'LOSSLESS-DELIVERY.json').read_text())
    decoded={}
    for item in ledger['encodings']:
        zipped=(root/item['delivered_path']).read_bytes(); check_bytes(zipped,item['delivered'])
        with gzip.GzipFile(fileobj=__import__('io').BytesIO(zipped)) as stream:
            raw=stream.read(item['raw']['bytes']+1)
        check_bytes(raw,item['raw']); decoded[item['raw_path']]=raw
        target=root/item['raw_path']
        if target.exists(): check_bytes(target.read_bytes(),item['raw'])
        elif not args.verify_only:
            fd,name=tempfile.mkstemp(prefix='.restore-',dir=target.parent)
            try:
                with os.fdopen(fd,'wb') as f: f.write(raw)
                os.replace(name,target)
            finally:
                if os.path.exists(name): os.unlink(name)
    for row in ledger['original_raw_inventory']:
        if args.verify_only and row['path'] in decoded: data=decoded[row['path']]
        else: data=(root/row['path']).read_bytes()
        check_bytes(data,row)
    print(json.dumps({'status':'PASS','original_raw_files':len(ledger['original_raw_inventory']),'mode':'decode-only' if args.verify_only else 'restore-and-verify'}))
if __name__=='__main__': main()
