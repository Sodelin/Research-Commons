import time
from pathlib import Path
time.sleep(0.4)
Path("done").write_text("done")
