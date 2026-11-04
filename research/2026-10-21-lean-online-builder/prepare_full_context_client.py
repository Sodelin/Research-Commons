#!/usr/bin/env python3
"""Derive the bounded full-context client from the unchanged existing client.

Only explicit input/deadline limits and failed-run/progress metadata differ.
No acceptance predicate, server, toolchain, native profile or protocol changes.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    core = (ROOT / 'online_lean_quiet.mjs').read_bytes()
    if sha(core) != 'ba32b4ee63052bbdfd8a90d385cd5c764096c07ed2ab536fe00796f7bce1aca3':
        raise ValueError('ORIGINAL_CLIENT_CHANGED')
    patches = [
        ('Buffer.byteLength(source) > 262144', 'Buffer.byteLength(source) > 1048576'),
        ('timeoutMs = 60000', 'timeoutMs = 300000'),
        ('lastProgress = { processing_ranges: ranges.length, furthest_end_line: furthestLine };',
         'lastProgress = { processing_ranges: ranges.length, furthest_end_line: furthestLine,\n'
         '            first_processing_ranges: ranges.slice(0, 12).map(r => ({\n'
         '              start: r.range?.start ?? null, end: r.range?.end ?? null, kind: r.kind ?? null })) };'),
        ('reject(Object.assign(err, { observations, capture_stats: captureStats() }));',
         'reject(Object.assign(err, { observations, capture_stats: captureStats(),\n'
         '        source_sha256: sha(source), source_bytes: Buffer.byteLength(source),\n'
         '        submitted_source_sha256: sha(text), before }));'),
        ("report = { status: 'UNVERIFIED', reason: error.message, observations: error.observations ?? [], capture_stats: error.capture_stats ?? null };",
         "report = { status: 'UNVERIFIED', reason: error.message, observations: error.observations ?? [],\n"
         '    capture_stats: error.capture_stats ?? null, source_sha256: error.source_sha256 ?? null,\n'
         '    source_bytes: error.source_bytes ?? null, submitted_source_sha256: error.submitted_source_sha256 ?? null,\n'
         '    before: error.before ?? null };'),
    ]
    selected = core.decode()
    for before, after in patches:
        if selected.count(before) != 1:
            raise ValueError('EXACT_REVIEWED_CLIENT_HUNK_REQUIRED')
        selected = selected.replace(before, after, 1)
    reverse = selected
    for before, after in reversed(patches):
        if reverse.count(after) != 1:
            raise ValueError('CLIENT_PATCH_NOT_REVERSIBLE')
        reverse = reverse.replace(after, before, 1)
    if reverse != core.decode():
        raise ValueError('OTHER_PROTOCOL_OR_ACCEPTANCE_CHANGE')
    header = ('/** Explicit full-context variant:1MiB source/300s document deadline.\n'
              ' * Bounded pending-range locations and failure input/version bindings\n'
              ' * aid diagnosis. Existing proof protocol and acceptance stay exact.\n'
              ' * Native/controller admission is separate. */\n')
    raw = (header + selected).encode()
    drain = (ROOT / 'online_lean_drain.mjs').read_bytes()
    if sha(drain) != '034029ffdf53af6e0d595c2ee92c73abd572275531d9698ba968070b8dd8ff6e':
        raise ValueError('ORIGINAL_DRAIN_CHANGED')
    entry = drain.replace(b"'./online_lean_quiet.mjs'", b"'./online_lean_full_context.mjs'", 1)
    for parent in [ROOT, ROOT / 'public-packet']:
        (parent / 'online_lean_full_context.mjs').write_bytes(raw)
        (parent / 'online_lean_full_context_drain.mjs').write_bytes(entry)
    review = {
        'schema': 'full_context_client_exact_variant_v2',
        'original_core_sha256': sha(core), 'variant_sha256': sha(raw),
        'variant_bytes': len(raw), 'drain_sha256': sha(entry),
        'exact_reversible_patches': [{'before': a, 'after': b} for a, b in patches],
        'all_other_protocol_and_acceptance_body_byte_identical': True,
        'source_input_bound_bytes': 1048576, 'document_deadline_ms': 300000,
        'parent_deadline_seconds': 370, 'progress_ranges_retained_max': 12,
        'failed_run_status_stays_unverified': True,
        'native_profile_or_original_client_changed': False,
        'compiler_or_hosted_call_run_by_preparer': False,
    }
    (ROOT / 'public-packet/FULL-CONTEXT-CLIENT-EXACT-PATCHES.json').write_text(
        json.dumps(review, indent=2) + '\n')
    print(json.dumps({'variant_sha256': sha(raw), 'variant_bytes': len(raw),
                      'only_explicit_hunks_changed': len(patches), 'compiler_invoked': False}))


if __name__ == '__main__':
    main()
