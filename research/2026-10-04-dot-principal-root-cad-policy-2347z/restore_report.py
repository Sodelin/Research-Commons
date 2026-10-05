#!/usr/bin/env python3
"""Restore one lossless source-policy certificate and verify its original hash."""
from pathlib import Path
import gzip,hashlib
p=Path(__file__).resolve().parent/'package'/'CAD-ASSEMBLED-POLICY-RECEIPT.json'
b=gzip.decompress((p.parent/(p.name+'.gz')).read_bytes())
assert len(b)==12425328 and hashlib.sha256(b).hexdigest()=="1d3a3565070f05472c0355bd347866d8807600189e814806016326bcdcd1bc9d"
if p.exists():assert p.read_bytes()==b,"An existing different report will not be overwritten."
else:p.write_bytes(b)
print("Original recorded certificate restored byte-exactly; this performs no solver validation.")
