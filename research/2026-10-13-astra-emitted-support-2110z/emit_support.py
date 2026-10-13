#!/usr/bin/env python3
"""Emit literal conditional distinct-support proofs; generation is not compilation."""
import argparse
import hashlib
import importlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / '2026-10-13-astra-unified-solver-0645z'
ADAPTER = HERE.parent / '2026-10-13-astra-positive-support-adapter-0830z'
PINS = {
    BASE / 'certificates.py': 'ce6ba92566e5ee009ca565476744db65555160f0e4a7d32b70ee07505b57f0b3',
    BASE / 'emit_lean.py': '27264a92409966415094b902df8226e7a86f305c0cef148325c7f6f60795ae37',
    ADAPTER / 'lean/Astra/PositiveSupportAdapter.lean': '29782b7ff42fefd5b1634e20ea1f0c695714e5cd625c2730a255bbda656ab479',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dependencies():
    for path, expected in PINS.items():
        if sha(path) != expected:
            raise ValueError('selected dependency differs: ' + str(path))
    sys.path.insert(0, str(BASE))
    try:
        certificate_module = importlib.import_module('certificates')
        emitter = importlib.import_module('emit_lean')
    finally:
        sys.path.pop(0)
    for module, name in [(certificate_module, 'certificates.py'), (emitter, 'emit_lean.py')]:
        if Path(module.__file__).resolve() != BASE / name:
            raise ValueError('selected module was shadowed: ' + name)
    return certificate_module, emitter


def render(certificate):
    """Reuse the unchanged emitter and add exact polynomial-to-grid binding."""
    api, emitter = dependencies()
    result = api.checked(certificate)
    level = result['level']
    ident = api.digest(certificate)
    base_text = emitter.render(certificate)
    coefficient_values = [api.rational(value) for value in certificate['coefficients']]
    powers = [k * (k - 1) // 2 for k in range(1, level + 1)]
    # This is the same deterministic literal nonzero point used by the pinned
    # emitter. Its nonzeroness is subsequently proved by Lean's norm_num.
    point = next(x for x in range(max(powers) + 1)
                 if sum(c * x ** e for c, e in zip(coefficient_values, powers)))
    coefficient_expression = ''.join(
        'if k = ' + str(k) + ' then ' + emitter.real(value) + ' else '
        for k, value in enumerate(coefficient_values, start=1)) + '0'
    levels = '{' + ', '.join(map(str, range(1, level + 1))) + '}'
    lines = [
        'import Certificate_' + ident,
        'import Astra.PositiveSupportAdapter',
        '',
        '/- Exact certificate identity: ' + ident + '.',
        'Conditional distinct positive-mass values only; generation is not compilation. -/',
        'namespace Astra.GeneratedSupport.Certificate_' + ident,
        'open Astra.Generated.Certificate_' + ident,
        'open Astra.PositiveSupportAdapter',
        'open DotG4.ActualObservableBankCertificate',
        'open DotG4.ActualSparseCertificateExistence',
        'open scoped BigOperators',
        '',
        'noncomputable def coefficients (k : Nat) : ℝ := ' + coefficient_expression,
        '',
        'lemma levels_eq : momentLevels ' + str(level) + ' = ' + levels + ' := by',
        '  ext k',
        '  simp only [momentLevels, Finset.mem_image, Finset.mem_univ, true_and,',
        '    Finset.mem_insert, Finset.mem_singleton]',
        '  constructor',
        '  · rintro ⟨n, rfl⟩',
        '    have hn := n.isLt',
        '    omega',
        '  · intro h',
    ]
    if level > 1:
        lines.append('    rcases h with ' + ' | '.join(['h'] * level))
    for k in range(level):
        indent = '    ' if level == 1 else '    · '
        lines.append(indent + 'subst k')
        lines.append(('    ' if level == 1 else '      ') +
                     'exact ⟨⟨' + str(k) + ', by decide⟩, rfl⟩')
    lines += [
        '',
        'theorem polynomial_identity (x : ℝ) :',
        '    polynomial x = (sparsePolynomial (momentLevels ' + str(level) +
        ') coefficients).eval x := by',
        '  rw [sparsePolynomial_eval, levels_eq]',
        '  norm_num [coefficients, polynomial]',
        '',
        'theorem distinct_positive_support_bound {A : Type*} [Fintype A]',
        '    (weight value : A → ℝ)',
        '    (hw : ∀ a, 0 ≤ weight a)',
        '    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)',
    ]
    for i, (power, moment) in enumerate(zip(powers, certificate['moments'])):
        lines.append('    (moment' + str(i) + ' : ∑ a, weight a * (value a)^' +
                     str(power) + ' = ' + emitter.real(api.rational(moment)) + ')')
    lines += [
        '    : (positiveSupportValues weight value).card ≤ ' + str(level - 1) + ' := by',
        '  apply positive_support_card_le_pred ' + str(level) +
        ' coefficients polynomial polynomial_identity ' + str(point) +
        ' nonzero_value weight value',
        '  intro a ha',
        '  exact finite_supported_bank weight value hw hv ' +
        ' '.join('moment' + str(i) for i in range(level)) + ' a ha',
        '',
        '#print axioms levels_eq',
        '#print axioms polynomial_identity',
        '#print axioms distinct_positive_support_bound',
        'end Astra.GeneratedSupport.Certificate_' + ident,
        '',
    ]
    return ident, base_text, '\n'.join(lines), dict(
        level=level, exponents=powers, nonzero_test_point=point,
        support_cap=level - 1, certificate_sha256=ident)


def emit(certificate, output):
    ident, base_text, support_text, mathematical_interface = render(certificate)
    output = Path(output)
    output.mkdir(parents=False, exist_ok=False)
    files = {}
    for filename, source in [('Certificate_' + ident + '.lean', base_text),
                             ('Support_' + ident + '.lean', support_text)]:
        path = output / filename
        with path.open('x') as stream:
            stream.write(source)
        files[filename] = dict(bytes=path.stat().st_size, sha256=sha(path))
    manifest = dict(schema='astra_literal_support_emission_v1',
                    mathematical_interface=mathematical_interface,
                    files=files, selected_dependencies={str(p.relative_to(HERE.parent)): h
                                                      for p, h in PINS.items()},
                    emitter_sha256=sha(Path(__file__)), compiled=False,
                    source_existence_certified=False,
                    physical_representative_certified=False,
                    native_refinement_proved=False,
                    zero_mass_domain='stronger inherited all-atom premise retained',
                    binding='literal original moments required of the same finite bank')
    with (output / 'EMISSION.json').open('x') as stream:
        json.dump(manifest, stream, indent=2)
        stream.write('\n')
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    api, _ = dependencies()
    with args.certificate.open('rb') as stream:
        certificate = api.loads(stream.read(api.MAX_BYTES + 1))
    print(json.dumps(emit(certificate, args.output)))


if __name__ == '__main__':
    main()
