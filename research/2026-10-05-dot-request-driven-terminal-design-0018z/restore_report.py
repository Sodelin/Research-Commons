#!/usr/bin/env python3
"""Restore one original recorded policy receipt; no backend validation."""
from pathlib import Path
import gzip,hashlib
p=Path(__file__).resolve().parent/'package'/'REQUEST-POLICY-RECEIPT.json'
b=gzip.decompress((p.parent/(p.name+'.gz')).read_bytes())
assert len(b)==12448784 and hashlib.sha256(b).hexdigest()=="c768cb6de607e5551a6053a860870897f9d28c3ed0bbbeb717ebb2dfbf749bd1"
if p.exists():assert p.read_bytes()==b,"An existing different report will not be overwritten."
else:p.write_bytes(b)
print("Original recorded certificate restored byte-exactly; no solver execution.")
