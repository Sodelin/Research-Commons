#!/usr/bin/env python3
"""Complete read-only official namespace, reserving exactly four owned modules."""
import argparse,hashlib,importlib.util,json,shutil
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
AUTH=ROOT/'scripts/build_with_authenticated_overlay.py'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(AUTH)=='ffc577ca31389936554dd64b53664452f6274b910fc5508b6c246a5709a993cc'
spec=importlib.util.spec_from_file_location('pinned_authenticated_overlay',AUTH)
auth=importlib.util.module_from_spec(spec);spec.loader.exec_module(auth)

class DesktopBuilder(auth.OverlayBuilder):
    def __init__(self):
        super().__init__()
        source=self.overlay_external
        view=ROOT/'.build/official-namespace-view'
        owned=auth.original.OWNED_MATHLIB
        protected=[tuple(m.split('.')) for m in owned]
        skipped=[];links=[]
        def stage(src,dst,parts):
            assert not dst.is_symlink();dst.mkdir(exist_ok=True,parents=True)
            for child in sorted(src.iterdir()):
                rel=parts+(child.name,);out=dst/child.name
                if child.is_dir() and any(rel==p[:len(rel)] for p in protected):
                    stage(child,out,rel)
                elif child.is_file() and any(parts==p[:-1] and child.name.startswith(p[-1]+'.') for p in protected):
                    skipped.append({'relative':str(Path(*rel)),'sha256':sha(child),'bytes':child.stat().st_size})
                else:
                    target=child.resolve(strict=True)
                    if out.is_symlink():assert out.resolve(strict=True)==target
                    else:
                        assert not out.exists();out.symlink_to(target,target_is_directory=child.is_dir())
                    links.append({'relative':str(Path(*rel)),'target':str(target),'directory':child.is_dir()})
        stage(source,view,())
        for module,want in owned.items():
            assert sha(ROOT/'source-store'/(want+'.lean'))==want
            official=self.mathlib/(module.replace('.','/')+'.lean')
            assert sha(official)==want,('Owned upstream source differs',module)
        self.overlay_external=view
        self.external=[view if p==source else p for p in self.external]
        record={'status':'PASS_READONLY_NAMESPACE_MASK','wrapper_sha256':sha(Path(__file__)),'unchanged_authenticated_sha256':sha(AUTH),'original_external_root':str(source),'actual_filtered_external_root':str(view),'owned_exact_upstream_sources':owned,'omitted_official_files':skipped,'unmodified_official_links':links,'compiler_core_flags_resource_caps_proof_and_audit_unchanged':True,'official_cache_modified':False,'qualification':'Historical wrapper assumes four owned official modules are absent from external object root. Complete official cache requires this isolated filtered view. Lookup/bundle/inventory checks remain unchanged; all four project modules are freshly kernel checked.'}
        auth.original.core.save(self.run/'DESKTOP-NAMESPACE-MASK.json',record)
        shutil.copyfile(Path(__file__),self.run/'DESKTOP-WRAPPER.py')

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('target');args=ap.parse_args()
    b=DesktopBuilder();assert args.target in b.graph['targets'];raise SystemExit(b.run_targets([args.target]))
