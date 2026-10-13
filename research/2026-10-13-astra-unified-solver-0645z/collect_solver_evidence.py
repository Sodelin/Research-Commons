"""Preserve owned synthetic solver runs without duplicating pinned runtimes.

Only explicitly named scratch runs are copied. Never sweeps arbitrary user
directories. Runtime source is already public and bound by its source manifest.
"""
from pathlib import Path
import hashlib
import json
import shutil

HERE=Path(__file__).resolve().parent
RUNS={'initial-source':'astra-solver-tests-0645',
      'native-and-emitter':'astra-solver-native-tests-0645',
      'fixed-external-encoding':'astra-solver-encoded-tests-0645'}


def main():
    out=HERE/'evidence/solver-runs'
    out.mkdir(exist_ok=False)
    manifest=[]
    for label,directory in RUNS.items():
        source=Path('/workspace/scratch')/directory
        for p in sorted(source.rglob('*')):
            rel=p.relative_to(source)
            if not p.is_file() or 'runtime' in rel.parts or '__pycache__' in rel.parts:
                continue
            target=out/label/rel
            target.parent.mkdir(parents=True,exist_ok=True)
            data=p.read_bytes()
            target.write_bytes(data)
            manifest.append(dict(path=str(target.relative_to(HERE)),bytes=len(data),
                                 sha256=hashlib.sha256(data).hexdigest()))
    (out/'COPIED-ARTIFACTS.json').write_text(json.dumps(dict(
        source_runs=RUNS,files=manifest,
        omitted_runtime='Exact original source copies, bound by certified-bounds-sources.json; not new implementations.'),indent=2)+'\n')
    example=HERE/'examples'
    example.mkdir(exist_ok=False)
    source=Path('/workspace/scratch/astra-solver-encoded-tests-0645')
    for name in ['finite-witness','bounded-exhaustion','singleton-generator','correlated-menu','unencoded-tie']:
        shutil.copyfile(source/(name+'.json'),example/(name+'.json'))
    # Provisioning used only public official artifacts; preserve the exact
    # tool/dependency identities separately from the enclosing resource receipt.
    provision=HERE/'evidence/provisioned-identities'
    provision.mkdir(exist_ok=False)
    for source,name in [
        (Path('/workspace/scratch/astra-lean-0645/PROVISIONING.json'),'LEAN.json'),
        (Path('/workspace/scratch/astra-native-0645/packet/logs/PROVISIONING.json'),'RUST.json'),
        (Path('/workspace/scratch/astra-native-0645/packet/logs/BUILD-RESULT.json'),'BASELINE-NATIVE-BUILD.json'),
        (Path('/workspace/scratch/astra-native-0645/packet/signed-differential/RESULT.json'),'BASELINE-DIFFERENTIAL.json')]:
        shutil.copyfile(source,provision/name)
    print(json.dumps(dict(copied_solver_artifacts=len(manifest),status='PRESERVED')))


if __name__=='__main__':
    main()
