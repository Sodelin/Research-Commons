#!/usr/bin/env python3
"""Verify and unpack only the exact indexed configuration/evidence files.

Uses Python's standard library, never executes archive contents, never extracts
unlisted members or overwrites a differing existing file. Source-store Git blobs
are delivered separately and are not modified by this program.
"""
from pathlib import Path, PurePosixPath
import argparse,base64,hashlib,json,os,tarfile,tempfile
ROOT=Path(__file__).resolve().parents[1]
INDEX_SHA256='8c08d3aaeb0eeef36cd2c925e19af430d2d06b796841424d75ccd5619c392cb2'

def sha(data):return hashlib.sha256(data).hexdigest()
def require(ok,message):
    if not ok:raise RuntimeError(message)
def relative(name):
    p=PurePosixPath(name)
    require(not p.is_absolute() and name==str(p) and name not in ('','.')
            and '..' not in p.parts and '\\' not in name,'Unsafe or noncanonical artifact path.')
    return p

def write_exact(root,name,data):
    rel=relative(name);target=root.joinpath(*rel.parts)
    parent=root
    for part in rel.parts[:-1]:
        parent=parent/part
        require(not parent.is_symlink(),'Archive destination traverses a symlink.')
        parent.mkdir(exist_ok=True)
        require(parent.is_dir(),'Archive destination parent is not a directory.')
    require(not target.is_symlink(),'Refusing existing symlink destination.')
    if target.exists():
        require(target.is_file() and target.read_bytes()==data,'Existing file differs; preserved without overwrite: '+name)
        return
    with target.open('xb') as out:
        out.write(data);out.flush();os.fsync(out.fileno())
    require(target.read_bytes()==data,'Written file verification failed; file retained for inspection.')

def unpack(destination,verify_only=False,package=ROOT):
    rawindex=(package/'DELIVERY-ARTIFACT-INDEX.json').read_bytes()
    require(sha(rawindex)==INDEX_SHA256,'Index hash differs.')
    index=json.loads(rawindex);expected={x['path']:x for x in index['decoded_contents']}
    require(len(expected)==len(index['decoded_contents'])==index['decoded_files'],'Duplicate/missing indexed member.')
    for name,row in expected.items():
        relative(name);require(row['bytes']>=0,'Invalid member size.')
    require(sum(x['bytes'] for x in expected.values())==index['decoded_bytes'],'Decoded size total differs.')
    destination=destination.resolve()
    if not verify_only:destination.mkdir(parents=True,exist_ok=True)
    seen=set();total=0;compressed_hash=hashlib.sha256()
    with tempfile.TemporaryFile() as archive:
        for part in index['parts']:
            rel=relative(part['path']);text=package.joinpath(*rel.parts).read_bytes()
            require(len(text)==part['bytes'] and sha(text)==part['sha256'],'Encoded part differs.')
            body=base64.b64decode(text.strip(),validate=True);total+=len(body)
            require(total<=index['compressed_bytes'],'Compressed size exceeds pin.')
            compressed_hash.update(body);archive.write(body)
        require(total==index['compressed_bytes'] and compressed_hash.hexdigest()==index['compressed_sha256'],
                'Compressed artifact identity differs.')
        archive.seek(0)
        with tarfile.open(fileobj=archive,mode='r:xz') as tar:
            for member in tar:
                relative(member.name)
                require(member.isfile() and not member.issym() and not member.islnk(),'Non-regular member rejected.')
                require(member.name not in seen,'Duplicate tar member rejected.');seen.add(member.name)
                if member.name=='CONTENTS.json':
                    require(member.size<1024*1024,'Contents manifest exceeds bounded size.')
                    body=tar.extractfile(member).read(member.size+1)
                    require(len(body)==member.size and sha(body)==index['contents_manifest_sha256'],'Contents manifest differs.')
                    continue
                require(member.name in expected,'Unlisted member rejected.')
                row=expected[member.name];require(member.size==row['bytes'],'Member size differs.')
                body=tar.extractfile(member).read(member.size+1)
                require(len(body)==row['bytes'] and sha(body)==row['sha256'],'Member bytes differ.')
                if not verify_only:write_exact(destination,member.name,body)
    require(seen==set(expected)|{'CONTENTS.json'},'Archive coverage differs.')
    result={'status':'PASS_VERIFY_ONLY' if verify_only else 'PASS_EXACT_UNPACK',
            'index_sha256':INDEX_SHA256,'files_verified':len(expected),'decoded_bytes':index['decoded_bytes'],
            'compiled_or_executed_archive_contents':False,'differing_existing_files_overwritten':False}
    if not verify_only:write_exact(destination,'UNPACK-RESULT.json',(json.dumps(result,indent=2)+'\n').encode())
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--verify-only',action='store_true')
    p.add_argument('--destination',type=Path,default=ROOT);a=p.parse_args()
    print(json.dumps(unpack(a.destination,a.verify_only)))
