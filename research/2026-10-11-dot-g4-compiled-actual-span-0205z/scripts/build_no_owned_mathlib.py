"""Specialize the authenticated namespace overlay to a graph with no owned Mathlib modules."""
from pathlib import Path
import importlib.util,json,hashlib,sys
P=Path(__file__).resolve().parents[1]
g=json.loads((P/'DEPENDENCY-GRAPH.json').read_bytes())
assert not any(m.startswith('Mathlib.') for t in g['targets'].values() for m in t['modules'])
a=P/'scripts/build_with_authenticated_overlay.py'
assert hashlib.sha256(a.read_bytes()).hexdigest()=='ffc577ca31389936554dd64b53664452f6274b910fc5508b6c246a5709a993cc'
spec=importlib.util.spec_from_file_location('authenticated_empty_owned_overlay',a);auth=importlib.util.module_from_spec(spec);spec.loader.exec_module(auth)
assert len(auth.original.OWNED_MATHLIB)==4
# No project source occupies the Mathlib namespace in this profile. The complete
# pinned official namespace is retained; all inventory/resolution checks remain.
auth.original.OWNED_MATHLIB={}
b=auth.OverlayBuilder()
auth.original.core.save(b.run/'EMPTY-OWNED-MATHLIB-PINS.json',{'specialization_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'graph_sha256':b.graph_sha,'owned_mathlib_modules':[],'complete_official_namespace_retained':True,'inherited_inventory_resolution_companion_kernel_and_audit_checks_unchanged':True})
(b.run/'EMPTY-OWNED-MATHLIB-WRAPPER.py').write_bytes(Path(__file__).read_bytes())
raise SystemExit(b.run_targets([sys.argv[1]]))
