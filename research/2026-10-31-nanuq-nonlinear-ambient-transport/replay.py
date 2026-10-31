import hashlib, os, pathlib, subprocess, sys
if len(sys.argv) < 4:
    raise SystemExit('usage: replay.py LEAN OUTPUT_DIR DEPENDENCY_LIB_DIR...')
base = pathlib.Path(__file__).resolve().parent
src = base / 'AmbientTransport.lean'
expected = 'da8602339db6b3c5e33ae4ab428f7ebff680646e7829e7fcb9b7e8307e19c635'
assert hashlib.sha256(src.read_bytes()).hexdigest() == expected
out = pathlib.Path(sys.argv[2]).resolve()
out.mkdir(parents=True, exist_ok=True)
env = dict(os.environ, LEAN_PATH=os.pathsep.join(str(pathlib.Path(p).resolve()) for p in sys.argv[3:]))
r = subprocess.run([str(pathlib.Path(sys.argv[1]).resolve()), '-o', str(out / 'AmbientTransport.olean'), src.name], cwd=base, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(out / 'replay.log').write_bytes(r.stdout)
(out / 'replay.exit').write_text(str(r.returncode) + '\n')
sys.stdout.buffer.write(r.stdout)
raise SystemExit(r.returncode)
