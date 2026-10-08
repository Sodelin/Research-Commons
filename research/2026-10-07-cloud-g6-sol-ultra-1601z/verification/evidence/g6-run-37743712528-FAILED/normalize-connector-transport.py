"""Static outer connector transport normalization; never invokes Lean."""
from pathlib import Path
import re,sys
raw=Path(sys.argv[1]).read_bytes()
clean='\n'.join(re.sub(r'^\ufeff?\d{4}-\d{2}-\d{2}T\S+ ', '', line) for line in raw.decode().splitlines())+'\n'
Path(sys.argv[2]).write_bytes(clean.encode())
