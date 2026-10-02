#!/usr/bin/env python3
"""Fetch only four pinned official artifacts; do not execute install scripts."""
import pathlib,urllib.request,hashlib,tarfile,zipfile,io
R=pathlib.Path(__file__).resolve().parents[1]; V=R/'vendor';V.mkdir(exist_ok=True)
items=[
 ('cvc5-Linux-x86_64-static.zip','https://github.com/cvc5/cvc5/releases/download/cvc5-1.4.1/cvc5-Linux-x86_64-static.zip','2f8efe58fe27ba7bccbb504533f690b9312d69da14192712460e4a19231f02a1'),
 ('cvc5-1.4.1-source.tgz','https://codeload.github.com/cvc5/cvc5/tar.gz/refs/tags/cvc5-1.4.1','5448e82682a65ddbdd7148402f73d48725252e70c9a0e43999c3f305bfbb4f76'),
 ('ethos-08e4aa40c4f8a6e00833f10e8d8985777e424027.tgz','https://codeload.github.com/cvc5/ethos/tar.gz/08e4aa40c4f8a6e00833f10e8d8985777e424027','c09435449873f12c15a2fa665b614ede222d4af506532affc57cd02f446b03b1'),
 ('logos-49f4fd1f256f5504f1a21c61c1808ffc56eeb6b8.tgz','https://codeload.github.com/cvc5/logos/tar.gz/49f4fd1f256f5504f1a21c61c1808ffc56eeb6b8','7393a1c21799749b48e3270af9a13605edbcc3ef726acdda5e207d96dc9479f1')]
for name,url,digest in items:
 p=V/name
 b=p.read_bytes() if p.exists() else urllib.request.urlopen(url,timeout=30).read()
 if hashlib.sha256(b).hexdigest()!=digest:raise ValueError('hash mismatch '+name)
 p.write_bytes(b)
 if name.endswith('.zip'):
  with zipfile.ZipFile(io.BytesIO(b)) as z:
   if any(pathlib.PurePosixPath(n).is_absolute() or '..' in pathlib.PurePosixPath(n).parts for n in z.namelist()):raise ValueError('unsafe zip')
   z.extractall(V)
 else:
  with tarfile.open(fileobj=io.BytesIO(b),mode='r:gz') as t:
   members=t.getmembers()
   if name=='cvc5-1.4.1-source.tgz':members=[m for m in members if '/proofs/eo/cpc/' in m.name or m.name.endswith('/contrib/check-logos-compilation')]
   t.extractall(V,members=members,filter='data')
 print(name,digest,flush=True)
(V/'cvc5-Linux-x86_64-static/bin/cvc5').chmod(0o755)
