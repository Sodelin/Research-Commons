#!/usr/bin/env python3
"""Emit an uncompiled input-only SuppliedCombCertificates (Fin n) record.

Reuses frozen exact parsing, checking and proof generation. This is not a
physical decision, native refinement, or an invocation of Lean/Lake.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import types

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = 'research/2026-10-13-astra-unified-solver-0645z/'
SUPPORT = 'research/2026-10-13-astra-emitted-support-2110z/'
MAX_OUTPUT_BYTES = 16 * 1024**2
MAX_UNIQUE_CERTIFICATES = 64
ASSEMBLER_SHA256 = 'b728c6a9b05804082be97127535894b42c65b3b6aa13f75fb01a6808e69f31e1'
MODULE_PATHS = {
    'certificates': BASE + 'certificates.py',
    'emit_lean': BASE + 'emit_lean.py',
    'emit_support': SUPPORT + 'emit_support.py',
    'external_encoding': BASE + 'external_encoding.py',
}
PINS = {
    BASE + 'certificates.py': 'ce6ba92566e5ee009ca565476744db65555160f0e4a7d32b70ee07505b57f0b3',
    BASE + 'emit_lean.py': '27264a92409966415094b902df8226e7a86f305c0cef148325c7f6f60795ae37',
    SUPPORT + 'emit_support.py': '6e7dc1faea63642464b802b59aceed7c809ea2f5148abb62bca36dab9b11bfdd',
    BASE + 'external_encoding.py': '78dfd11a8157a5102c520be85a5fc42f4b4137250846ce510df9df98a90f4d69',
    BASE + 'lean/Astra/CommonCertificateKernel.lean': '1f35f9e11cef727b27ed30230a390ada2a32dfc50733ea0d4cb172fb7c053266',
    'research/2026-10-13-astra-positive-support-adapter-0830z/lean/Astra/PositiveSupportAdapter.lean':
        '29782b7ff42fefd5b1634e20ea1f0c695714e5cd625c2730a255bbda656ab479',
    'research/2026-10-13-dot-g3-certified-consumer-0631z/G3CertifiedCommonBoundedWitness.lean':
        '400153aac6adeb8905447f38c616a7d4008605668ffb2d2846dc9a9d5673f94c',
    'research/2026-10-14-astra-exact-0616-provider-recovery-0555z/source/G4ProtectedCommonRepresentative.lean':
        '0616f81343ea0ef724bd874cfb8c94f2f67fdaff7ca462451f31aae47db98b04',
}


class Unavailable(RuntimeError):
    """Valid input cannot be emitted within this authenticated bounded profile."""


def sha(data):
    return hashlib.sha256(data).hexdigest()


def dependencies():
    """Execute only the pinned provider bytes; reject preloaded module ambiguity."""
    bodies = {}
    for name, expected in PINS.items():
        path = ROOT / name
        if path.is_symlink():
            raise Unavailable('selected dependency is a symlink: ' + name)
        data = path.read_bytes()
        if sha(data) != expected:
            raise Unavailable('selected dependency differs: ' + name)
        bodies[name] = data
    loaded = {}
    for name, relative in MODULE_PATHS.items():
        path = ROOT / relative
        old = sys.modules.get(name)
        if old is not None:
            if (getattr(old, '__file__', None) != str(path) or
                    getattr(old, '_astra_verified_source_sha256', None) != PINS[relative]):
                raise Unavailable('preloaded module is not this verified provider: ' + name)
            loaded[name] = old
            continue
        module = types.ModuleType(name)
        module.__file__ = str(path)
        sys.modules[name] = module
        try:
            exec(compile(bodies[relative], str(path), 'exec'), module.__dict__)
        except BaseException:
            sys.modules.pop(name, None)
            raise
        module._astra_verified_source_sha256 = PINS[relative]
        loaded[name] = module
    return loaded


def json_bytes(value, limit=MAX_OUTPUT_BYTES):
    """Bound accepted serialized bytes without first allocating the whole JSON."""
    result = bytearray()
    for part in json.JSONEncoder(indent=2, sort_keys=True, ensure_ascii=True).iterencode(value):
        encoded = part.encode('ascii')
        if len(result) + len(encoded) + 1 > limit:
            raise Unavailable('emission exceeds the bounded output profile')
        result.extend(encoded)
    result.extend(b'\n')
    return bytes(result)


def finite_table(entries):
    """Literal total Fin n table. No graph index or fallback for a real index."""
    result = 'Fin.elim0'
    for entry in reversed(entries):
        result = '(Fin.cases (' + entry + ') (' + result + '))'
    return result


def row_source(certificate, ident, emitter):
    level = certificate['level']
    real = emitter.real
    base = 'Astra.Generated.Certificate_' + ident
    support = 'Astra.GeneratedSupport.Certificate_' + ident
    values = ''.join('if k = ' + str(k) + ' then ' + real(value) + ' else '
                     for k, value in enumerate(certificate['moments'], 1)) + '0'
    literal_sum = emitter.sum_expr([real(c) + ' * ' + real(y)
                                   for c, y in zip(certificate['coefficients'], certificate['moments'])])
    return '\n'.join([
        'import Support_' + ident,
        'import Astra.SuppliedCombCertificateAssembly', '',
        '/- Literal input-only certificate; generation is not compilation. -/',
        'namespace Astra.GeneratedSuppliedRow.Certificate_' + ident,
        'open DotG3.CertifiedCommonBoundedWitness',
        'open DotG4.ActualObservableBankCertificate DotG4.ActualSparseCertificateExistence',
        'open scoped BigOperators', '',
        'noncomputable def values (k : Nat) : ℝ := ' + values, '',
        'noncomputable def certificate : SuppliedCombCertificates Unit where',
        '  level _ := ' + str(level),
        '  value _ := values',
        '  coeff _ := ' + support + '.coefficients',
        '  level_pos _ := by decide',
        '  nonzero := by',
        '    intro _ hz',
        '    apply ' + base + '.nonzero_value',
        '    rw [' + support + '.polynomial_identity, hz, Polynomial.eval_zero]',
        '  nonnegative := by',
        '    intro _ x hx',
        '    rw [← ' + support + '.polynomial_identity]',
        '    exact ' + base + '.nonnegative x hx.1 hx.2',
        '  annihilates := by',
        '    intro _',
        '    change (∑ k ∈ momentLevels ' + str(level) + ', ' + support + '.coefficients k * values k) = 0',
        '    calc',
        '      _ = ' + literal_sum + ' := by',
        '        rw [' + support + '.levels_eq]',
        '        norm_num [' + support + '.coefficients, values]',
        '      _ = 0 := ' + base + '.annihilation', '',
        '#check certificate', '#print axioms certificate',
        'end Astra.GeneratedSuppliedRow.Certificate_' + ident, '',
    ])


def menu_source(menu, ident, api, emitter):
    taxa = menu['taxa']
    by_pair = {(row['i'], row['j']): row['certificate'] for row in menu['pairs']}
    ids = sorted({api.digest(c) for c in by_pair.values()})
    n = len(taxa)
    rows, identities = [], []
    for i in taxa:
        rows.append(finite_table(['Astra.GeneratedSuppliedRow.Certificate_' +
                    api.digest(by_pair[(i, j)]) + '.certificate' for j in taxa]))
        identities.append(finite_table([json.dumps(api.digest(by_pair[(i, j)])) for j in taxa]))
    lines = ['import SuppliedRow_' + h for h in ids] + [
        '', '/- All original ordered pairs, in the explicit original taxa-list order. -/',
        'namespace Astra.GeneratedSuppliedMenu.Menu_' + ident,
        'open DotG3.CertifiedCommonBoundedWitness',
        'open Astra.SuppliedCombCertificateAssembly', '',
        'def taxon : Fin ' + str(n) + ' → String := ' + finite_table([json.dumps(x) for x in taxa]),
        'def certificateId (ij : Fin ' + str(n) + ' × Fin ' + str(n) + ') : String :=',
        '  ' + finite_table(identities) + ' ij.1 ij.2',
        'noncomputable def row (ij : Fin ' + str(n) + ' × Fin ' + str(n) + ') : SuppliedCombCertificates Unit :=',
        '  ' + finite_table(rows) + ' ij.1 ij.2',
        'noncomputable def supplied : SuppliedCombCertificates (Fin ' + str(n) + ') := assemble row', '',
    ]
    for i, taxon in enumerate(taxa):
        lines += ['theorem taxon_' + str(i) + ' : taxon ⟨' + str(i) + ', by decide⟩ = ' +
                  json.dumps(taxon) + ' := rfl']
    for index, pair in enumerate(menu['pairs']):
        i, j = taxa.index(pair['i']), taxa.index(pair['j'])
        cert = pair['certificate']
        ij = '(⟨' + str(i) + ', by decide⟩, ⟨' + str(j) + ', by decide⟩)'
        prefix = 'pair_' + str(index)
        lines += ['', 'theorem ' + prefix + '_id : certificateId ' + ij + ' = ' +
                  json.dumps(api.digest(cert)) + ' := rfl',
                  'theorem ' + prefix + '_level : supplied.level ' + ij + ' = ' + str(cert['level']) + ' := rfl']
        for field, key in [('coeff', 'coefficients'), ('value', 'moments')]:
            terms = [(0, '0')] + list(enumerate(cert[key], 1)) + [(cert['level'] + 1, '0')]
            for k, value in terms:
                expected = '0' if k == 0 or k == cert['level'] + 1 else emitter.real(value)
                lines += ['theorem ' + prefix + '_' + field + '_' + str(k) + ' : supplied.' + field +
                          ' ' + ij + ' ' + str(k) + ' = ' + expected + ' := rfl']
    lines += ['', '#check supplied', '#print axioms supplied',
              'end Astra.GeneratedSuppliedMenu.Menu_' + ident, '']
    return '\n'.join(lines)


def render_menu(raw):
    """Render bounded bytes, without creating output paths or running a compiler."""
    if type(raw) is not bytes:
        raise ValueError('the emission API requires original request bytes')
    providers = dependencies()
    api, support = providers['certificates'], providers['emit_support']
    menu = api.loads(raw)
    checked_menu = api.common_packet(menu)
    ident = api.digest(menu)
    by_digest = {}
    for row in menu['pairs']:
        by_digest.setdefault(api.digest(row['certificate']), row['certificate'])
    if len(by_digest) > MAX_UNIQUE_CERTIFICATES:
        raise Unavailable('too many distinct supplied certificates')
    payload, total = {}, 0

    def put(name, data):
        nonlocal total
        if name in payload:
            raise Unavailable('duplicate emitted path')
        if isinstance(data, str):
            data = data.encode('utf-8')
        if total + len(data) > MAX_OUTPUT_BYTES:
            raise Unavailable('emission exceeds the bounded output profile')
        payload[name] = data
        total += len(data)

    put('INPUT.json', raw)
    mathematical = {}
    for cert_id, certificate in sorted(by_digest.items()):
        actual, base_text, support_text, interface = support.render(certificate)
        if actual != cert_id:
            raise Unavailable('reused emitter changed the certificate identity')
        put('lean/Certificate_' + cert_id + '.lean', base_text)
        put('lean/Support_' + cert_id + '.lean', support_text)
        put('lean/SuppliedRow_' + cert_id + '.lean', row_source(certificate, cert_id, providers['emit_lean']))
        mathematical[cert_id] = interface
    bridge = HERE / 'lean/Astra/SuppliedCombCertificateAssembly.lean'
    bridge_bytes = bridge.read_bytes()
    if bridge.is_symlink() or sha(bridge_bytes) != ASSEMBLER_SHA256:
        raise Unavailable('selected input-record assembler differs')
    put('lean/Astra/SuppliedCombCertificateAssembly.lean', bridge_bytes)
    module_name = 'SuppliedMenu_' + ident
    put('lean/' + module_name + '.lean', menu_source(menu, ident, api, providers['emit_lean']))
    generated_modules = [name[5:-5].replace('/', '.') for name in sorted(payload)
                         if name.startswith('lean/') and name.endswith('.lean')]
    put('LAKE-TARGET.lean.inc', '\n'.join([
        '-- Additive target fragment only, not an executed or standalone Lake configuration.',
        '-- Requires owner-authenticated consumer/provider and kernel/support dependency routing.',
        'lean_lib AstraSuppliedCombMenu where', '  srcDir := "lean"',
        '  roots := #[`' + module_name + ']',
        '  globs := #[' + ', '.join('.one `' + name for name in generated_modules) + ']', '',
    ]))
    query_menu = providers['external_encoding'].fixed_queries(menu)
    put('FIXED-QUERIES.json', json_bytes(query_menu, MAX_OUTPUT_BYTES - total))
    references = []
    for index, row in enumerate(menu['pairs']):
        certificate = row['certificate']
        cert_id = api.digest(certificate)
        references.append(dict(
            original_pair_index=index, i=row['i'], j=row['j'],
            fin_i=menu['taxa'].index(row['i']), fin_j=menu['taxa'].index(row['j']),
            certificate_sha256=cert_id, certificate_original_tokens=certificate,
            normalized_coefficients=[str(api.rational(x)) for x in certificate['coefficients']],
            normalized_values=[str(api.rational(x)) for x in certificate['moments']],
            level=certificate['level'], exponents=mathematical[cert_id]['exponents'],
            declaration='Astra.GeneratedSuppliedRow.Certificate_' + cert_id + '.certificate',
            query_sha256s=[q['row_sha256'] for q in query_menu['queries']
                          if q['directed_pair'] == [row['i'], row['j']]]))
    ledger = dict(schema='astra_supplied_comb_input_ledger_v1',
                  input_bytes_sha256=sha(raw), canonical_menu_sha256=ident,
                  input_bytes=len(raw), taxa=[dict(fin=i, label=x) for i, x in enumerate(menu['taxa'])],
                  original_pair_order_preserved=True, typed_id_namespaces_preserved=True,
                  original_joint_configuration_table=menu['configurations'],
                  protected_edges=menu['protected_edges'], protected_hybrids=menu['protected_hybrids'],
                  parameter_constraints=menu['parameter_constraints'],
                  pair_references=references, distinct_certificate_count=len(by_digest),
                  certificate_hash_role='canonical original JSON token identity; no standalone original-byte slice is inferred',
                  raw_protected_count_role='declared PE+PH only; expanded physical h is not authenticated',
                  current_arithmetic_result=checked_menu,
                  fixed_query_sha256=sha(payload['FIXED-QUERIES.json']))
    put('IDENTITY-LEDGER.json', json_bytes(ledger, MAX_OUTPUT_BYTES - total))
    manifest = dict(schema='astra_supplied_comb_emission_v1', emission_status='EMITTED_UNCOMPILED',
                    status='UNKNOWN', compiled=False, source_existence_certified=False,
                    physical_representative_certified=False, native_refinement_proved=False,
                    hmatch_proved=False, expanded_protection_authenticated=False,
                    outer_admission_proved=False, parameter_feasibility_decided=False,
                    module=module_name,
                    declaration='Astra.GeneratedSuppliedMenu.Menu_' + ident + '.supplied',
                    type='DotG3.CertifiedCommonBoundedWitness.SuppliedCombCertificates (Fin ' + str(len(menu['taxa'])) + ')',
                    n=len(menu['taxa']), ordered_pair_count=len(menu['pairs']),
                    selected_provider_pins=PINS,
                    emitter_sha256=sha(Path(__file__).read_bytes()),
                    assembler_sha256=sha(bridge_bytes),
                    proposed_compile_status='Owner serial Lean/Lake receipt and type/axiom audit required',
                    payload=[dict(path=name, bytes=len(data), sha256=sha(data))
                             for name, data in sorted(payload.items())])
    put('EMISSION.json', json_bytes(manifest, MAX_OUTPUT_BYTES - total))
    return payload, manifest


def emit(raw, output):
    payload, manifest = render_menu(raw)
    output = Path(output)
    output.mkdir(parents=False, exist_ok=False)
    # Completed payload was bounded before the first write. An I/O interruption
    # leaves literal partial files; EMISSION is written last, never fabricated.
    for name, data in payload.items():
        path = output / name
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('xb') as stream:
            stream.write(data)
    return manifest


def main():
    import resource
    resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2,) * 2)
    resource.setrlimit(resource.RLIMIT_CPU, (30, 30))
    resource.setrlimit(resource.RLIMIT_FSIZE, (MAX_OUTPUT_BYTES,) * 2)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('menu', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    try:
        with args.menu.open('rb') as stream:
            raw = stream.read(262144 + 1)
        result = emit(raw, args.output)
        code = 0
    except Exception as error:
        api = sys.modules.get('certificates')
        refused = api is not None and isinstance(error, api.Refused)
        result = dict(status='REFUSED_INPUT' if refused else 'UNKNOWN',
                      emission_status='NOT_COMPLETED', reason=type(error).__name__ + ': ' + str(error),
                      compiled=False, source_existence_certified=False,
                      physical_representative_certified=False, native_refinement_proved=False)
        code = 1 if refused else 2
    print(json.dumps(result, sort_keys=True))
    return code


if __name__ == '__main__':
    raise SystemExit(main())
