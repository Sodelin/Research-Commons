"""Portable lookup of the exact public compiler pin."""
from pathlib import Path
import os, shutil, subprocess
EXPECTED='819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
def binary_dir():
    configured=os.environ.get('UNIFIED_LEAN_BIN')
    if configured:directory=Path(configured).expanduser().resolve()
    else:
        executable=shutil.which('lean')
        directory=Path(executable).resolve().parent if executable else None
    if directory is None:raise RuntimeError('Set UNIFIED_LEAN_BIN to the Lean4.33.1 bin directory')
    version=subprocess.check_output([str(directory/'lean'),'--version'],text=True)
    if '4.33.1' not in version or EXPECTED not in version:
        raise RuntimeError('Toolchain version/commit differs from the certified baseline: '+version)
    return directory
