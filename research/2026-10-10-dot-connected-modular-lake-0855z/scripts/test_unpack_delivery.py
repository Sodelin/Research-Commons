from pathlib import Path
import base64,hashlib,io,json,lzma,tarfile,tempfile
from unittest.mock import patch
import unpack_delivery as u

rows=[]
def check(name,fn,reject=False):
    try:fn()
    except (RuntimeError,FileExistsError):
        assert reject,name;rows.append({'name':name,'status':'PASS_REJECTED'})
    else:
        assert not reject,name;rows.append({'name':name,'status':'PASS'})
def fixture(root,names=None,duplicate=False):
    content=b'exact test body\n';members=names or [('one.txt',content)]
    contents=b'{}\n';out=io.BytesIO()
    with tarfile.open(fileobj=out,mode='w') as t:
        for name,body in [('CONTENTS.json',contents)]+members:
            i=tarfile.TarInfo(name);i.size=len(body);t.addfile(i,io.BytesIO(body))
    data=lzma.compress(out.getvalue());encoded=base64.b64encode(data)+b'\n';(root/'part.b64').write_bytes(encoded)
    index={'parts':[{'path':'part.b64','bytes':len(encoded),'sha256':u.sha(encoded)}],
           'compressed_bytes':len(data),'compressed_sha256':u.sha(data),
           'contents_manifest_sha256':u.sha(contents),'decoded_files':1,'decoded_bytes':len(content),
           'decoded_contents':[{'path':'one.txt','bytes':len(content),'sha256':u.sha(content)}]}
    raw=(json.dumps(index)+'\n').encode();(root/'DELIVERY-ARTIFACT-INDEX.json').write_bytes(raw);return u.sha(raw)
with tempfile.TemporaryDirectory() as d:
    p=Path(d);package=p/'package';package.mkdir();pin=fixture(package);dest=p/'destination'
    with patch.object(u,'INDEX_SHA256',pin):
        check('fresh_exact_unpack',lambda:u.unpack(dest,False,package))
        check('idempotent_exact_existing_files',lambda:u.unpack(dest,False,package))
        check('verify_only_no_output',lambda:u.unpack(p/'unused',True,package));assert not (p/'unused').exists()
        (dest/'one.txt').write_bytes(b'preserve different bytes')
        check('reject_differing_existing_file',lambda:u.unpack(dest,False,package),True)
        assert (dest/'one.txt').read_bytes()==b'preserve different bytes'
        encoded=(package/'part.b64').read_bytes();(package/'part.b64').write_bytes(encoded+b'A')
        check('reject_corrupt_encoded_part',lambda:u.unpack(p/'badpart',True,package),True)
        (package/'part.b64').write_bytes(encoded)
    with patch.object(u,'INDEX_SHA256','0'*64):
        check('reject_index_hash_drift',lambda:u.unpack(p/'badindex',True,package),True)
    for name in ['../escape','/absolute','a/../b','a//b','a\\b','']:
        check('reject_unsafe_path_'+repr(name),lambda n=name:u.relative(n),True)
    outside=p/'outside';outside.mkdir();symlinkroot=p/'links';symlinkroot.mkdir();(symlinkroot/'sub').symlink_to(outside,target_is_directory=True)
    check('reject_parent_symlink',lambda:u.write_exact(symlinkroot,'sub/file',b'x'),True)
    (symlinkroot/'file').symlink_to(outside/'file')
    check('reject_final_symlink',lambda:u.write_exact(symlinkroot,'file',b'x'),True)
    pin=fixture(package,[('two.txt',b'exact test body\n')])
    with patch.object(u,'INDEX_SHA256',pin):
        check('reject_unlisted_tar_member',lambda:u.unpack(p/'unlisted',True,package),True)
    pin=fixture(package,[('one.txt',b'exact test body\n'),('one.txt',b'exact test body\n')])
    with patch.object(u,'INDEX_SHA256',pin):
        check('reject_duplicate_tar_member',lambda:u.unpack(p/'duplicate',True,package),True)
actual=u.unpack(u.ROOT,True)
report={'status':'PASS','unpacker_sha256':u.sha(Path(u.__file__).read_bytes()),
        'test_sha256':u.sha(Path(__file__).read_bytes()),'controls':rows,'actual_artifact_verification':actual,
        'fresh_mathematical_replay_claimed':False}
(u.ROOT/'UNPACKER-TEST-RESULTS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':'PASS','controls':len(rows),'actual_files_verified':actual['files_verified']}))
