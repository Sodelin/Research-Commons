from pathlib import Path
import re,sys
raw=Path(sys.argv[1]).read_bytes()
text=raw.decode('utf-8')
clean='\n'.join(re.sub(r'^\d{4}-\d{2}-\d{2}T\S+ ', '', line) for line in text.splitlines())+'\n'
Path(sys.argv[2]).write_text(clean)
