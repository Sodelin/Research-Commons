"""Source-only integration of the retained loader for the exact current graph.

This adds no process controller or execution admission. The mandatory outer
refusal is unchanged. A future authenticated owner may use builder_type only
after binding every inherited writer. Direct execution stays a quiet refusal.
"""
from pathlib import Path
import hashlib
import json
import types

GRAPH = 'e3c299e538b6d956d5562243140d246246f121edcacc1c1bea9bd23bbb18811c'
SELECTION = 'f9f4845b86c4af93653d8661862fb2fac1ccc98fd3536b8b903e45a9c4702433'
TEMPLATE = 'f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a'
MATERIALS_GRAPH = 'ea10306d6d878bb56512d3417578eca5d83d23693655bb1740f258a501d2a4dd'
MATERIALS_SELECTION = '751beeae698e019ffbf09b16379be1730ebc37b4e00b544967524f8e4d3a01b3'
SOURCE_PROFILES = {
    (GRAPH, SELECTION): ('physical778', 755, 23),
    (MATERIALS_GRAPH, MATERIALS_SELECTION): ('materials10', 0, 10),
}
OUTER = '66a8c0b34d3eb0e7b0373007062160554745a8c3354a4a79019e293823b0d4d3'
SCRIPTS = {
    'build_connected.py': '13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc',
    'build_with_mathlib_overlay.py': '09b24ef22790f14e0fa7bc3ae6b0a9c2b1fe8d2d9cbfdfae5333b0dd566536c0',
    'build_with_authenticated_overlay.py': 'ffc577ca31389936554dd64b53664452f6274b910fc5508b6c246a5709a993cc',
    'build_desktop.py': 'a9d4d3f210eec5d01152661ca360e12cac295d8fdb1286ce99f548f307daf941',
    'build_streamed_audit.py': '748ea65d03736c89f6f868e431e00cdc9e21937273c227e9b5cc5c16a1e37ea1',
    'audit_stream.py': '398f7a2fef10fff0b1f50f02e10ce1a1ab860c352f2591fb3a769a1040fe96cd',
}


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def validated_targets(graph, labels):
    """Freeze a nonempty, known, unique ordered request before any builder work."""
    if not isinstance(labels, (list, tuple)):
        raise ValueError('NONEMPTY_KNOWN_UNIQUE_TARGETS_REQUIRED')
    selected = list(labels)
    if (not selected or any(not isinstance(k, str) for k in selected)
            or len(selected) != len(set(selected))
            or any(k not in graph['targets'] for k in selected)):
        raise ValueError('NONEMPTY_KNOWN_UNIQUE_TARGETS_REQUIRED')
    return selected


def select_targets(graph, requested):
    """Reuse Dot's target-selection policy at the restored loader boundary.

    Source: Research-Commons2ede2d4d, unified-lean-target-guard. The preserved
    core is13ee rather than that proposal's F74; no original core is patched.
    Selection is a source policy, never native/controller admission.
    """
    targets = graph['targets']
    if not isinstance(requested, str):
        raise ValueError('INVALID_TARGET_SELECTION')
    if requested == 'all':
        labels = list(targets)
    elif requested == 'accepted':
        labels = [k for k, v in targets.items()
                  if v.get('required_for_accepted_release', True)]
    elif requested == 'provisional':
        labels = [k for k, v in targets.items()
                  if not v.get('required_for_accepted_release', True)]
    else:
        labels = [requested]
    return validated_targets(graph, labels)


def profile_for(graph_raw, selection_raw, template_raw):
    """Exact authored inputs; no file/process/object/receipt admission."""
    specification = SOURCE_PROFILES.get((digest(graph_raw), digest(selection_raw)))
    if specification is None or digest(template_raw) != TEMPLATE:
        raise ValueError('EXACT_CURRENT_SOURCE_PROFILE_REQUIRED')
    profile_name, original_count, added_count = specification
    graph, selection = json.loads(graph_raw), json.loads(selection_raw)
    label, target = next(iter(graph['targets'].items()))
    original = {r['module'] for r in selection['sources']
                if r['source'] == 'original/current/connected'}
    added = {r['module']: r['sha256'] for r in selection['sources']
             if r['module'] not in original}
    if len(original) != original_count or len(added) != added_count:
        raise ValueError('CURRENT_ROLE_PARTITION_CHANGED')
    prefix = ''.join('import '+m+'\n' for m in target['roots'])
    marker = '#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]'
    template = template_raw.decode()
    if template.count(marker) != 1:
        raise ValueError('EXACT_AUDIT_MARKER_REQUIRED')
    audit = prefix + template.replace(marker, '#'+json.dumps(target['order'])).replace(
        '"AUDIT-OWNED.json"', '"AUDIT-RESULT.json"')
    return {
        'profile_name': profile_name, 'label': label,
        'original': frozenset(original), 'added': added,
        'targets': {k: {'required_for_accepted_release':
                       v.get('required_for_accepted_release', True)}
                    for k, v in graph['targets'].items()},
        # This exact label contains only characters retained by core.safe,
        # including its hyphens. Do not rename the original aggregate.
        'aggregate_name': 'Connected_'+label,
        'aggregate_sha256': digest(prefix.encode()),
        'audit_sha256': digest(audit.encode()),
        'owned_mathlib': {m: e['sha256'] for m, e in target['modules'].items()
                         if m.startswith('Mathlib.')},
    }


def invocation_allowed(profile, name, source_sha256, obj, seconds, memory, kind):
    """A fixed source/cap allowlist; true is not a controller capability."""
    if (seconds, memory) != (180, 4096):
        return False
    if kind == 'component':
        return (bool(obj) and name in profile['added']
                and profile['added'][name] == source_sha256)
    if kind == 'aggregate':
        return (bool(obj) and name == profile['aggregate_name']
                and source_sha256 == profile['aggregate_sha256'])
    if kind == 'complete-owned-audit':
        return (not obj and name == 'OwnedAudit'
                and source_sha256 == profile['audit_sha256'])
    return False


def read_profile(root):
    root = Path(root)
    paths = [root/'DEPENDENCY-GRAPH.json', root/'SOURCE-SELECTION.json',
             root/'scripts/AuditTemplate.lean', root/'start_new_context.sh']
    if any(p.is_symlink() for p in paths) or digest(paths[-1].read_bytes()) != OUTER:
        raise ValueError('SOURCE_OR_MANDATORY_REFUSAL_CHANGED')
    for name, wanted in SCRIPTS.items():
        path = root/'scripts'/name
        if path.is_symlink() or digest(path.read_bytes()) != wanted:
            raise ValueError('RETAINED_LOADER_SOURCE_CHANGED: '+name)
    return profile_for(*(p.read_bytes() for p in paths[:3]))


def builder_type(root, requested='accepted'):
    """Return the retained implementation with the exact current delta guard.

    No Builder is constructed here. Construction/invocation requires the
    actual original-owner controller outside this source-only proposal.
    """
    root = Path(root).resolve()
    profile = read_profile(root)
    # This precedes even loading the retained wrappers, and therefore precedes
    # Builder's cache/lock/record writes. The current default accepted is empty.
    selected = tuple(select_targets(profile, requested))
    source = root/'scripts/build_streamed_audit.py'
    module = types.ModuleType('exact_current_retained_streamed_loader')
    module.__file__ = str(source)
    exec(compile(source.read_bytes(), str(source), 'exec'), module.__dict__)
    # Same explicit namespace override used by the accepted1613 adapter.
    module.desktop.auth.original.OWNED_MATHLIB = profile['owned_mathlib']

    class CurrentDeltaBuilder(module.StreamedAuditBuilder):
        def __init__(self):
            read_profile(root)
            self.selected_targets = selected
            self.current_invocations = set()
            super().__init__()

        def run_targets(self, labels):
            checked = validated_targets(self.graph, labels)
            if tuple(checked) != selected:
                raise ValueError('TARGETS_DIFFER_FROM_PRECONSTRUCTION_SELECTION')
            return super().run_targets(checked)

        def invoke(self, name, source, obj, imports, context, seconds, memory, kind):
            if not invocation_allowed(profile, name, digest(source.read_bytes()),
                                      obj, seconds, memory, kind):
                raise ValueError('UNADMITTED_FRESH_INVOCATION: '+name)
            key = kind, name
            if key in self.current_invocations:
                raise ValueError('NO_SAME_RUN_INVOCATION_REPLAY: '+name)
            self.current_invocations.add(key)
            return super().invoke(name, source, obj, imports, context, seconds, memory, kind)

    return CurrentDeltaBuilder


if __name__ == '__main__':
    raise SystemExit(78)
