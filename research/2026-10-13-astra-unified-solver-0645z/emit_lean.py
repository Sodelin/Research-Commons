"""Generate kernel-checkable mathematical evidence from a checked certificate.

The output has no proof placeholders or computed native decision procedure.
Lean checks the literal arithmetic identities and a conditional finite-bank
support theorem. This is a per-certificate proof, not a compiler refinement or
a physical source-existence certificate. Generation alone is not compilation.
"""
from fractions import Fraction
from pathlib import Path
import argparse

from certificates import checked, digest, loads, rational


def real(q):
    q=Fraction(q)
    return f'(({q.numerator} : ℝ) / {q.denominator})'


def sum_expr(expressions):
    return '('+' + '.join(expressions)+')'


def render(certificate):
    checked(certificate)
    coeff=list(map(rational,certificate['coefficients']))
    moments=list(map(rational,certificate['moments']))
    powers=[k*(k-1)//2 for k in range(1,len(coeff)+1)]
    ident=digest(certificate)
    namespace='Certificate_'+ident
    p=lambda x:sum_expr([f'{real(c)} * ({x})^{e}' for c,e in zip(coeff,powers)])
    terms=[]
    for t in certificate['nonnegative_terms']:
        fields=[f'weight := {real(rational(t["weight"]))}',
                'left := '+str(bool(t['left'])).lower(),
                'right := '+str(bool(t['right'])).lower(),
                'square := ['+', '.join(real(rational(q)) for q in t['square'])+']']
        terms.append('({ '+', '.join(fields)+' } : SquareTerm)')
    values=[f'({t}).eval x' for t in terms]
    proof='h0'
    for i in range(1,len(terms)):
        proof=f'(add_nonneg {proof} h{i})'
    # A nonzero degree-d polynomial has at most d roots. We do not assume
    # that theorem in emitted proof: find a concrete nonzero value and prove
    # its exact value with norm_num. Bounded exhaustive d+1 integer probes.
    point=next(x for x in range(max(powers)+1)
               if sum(c*Fraction(x)**e for c,e in zip(coeff,powers)))
    lines=['import Astra.CommonCertificateKernel',
           '',f'/- Exact certificate SHA256: {ident}. Generation is not compilation. -/',
           f'namespace Astra.Generated.{namespace}',
           'open Astra.CommonCertificateKernel', 'open scoped BigOperators','',
           'noncomputable def polynomial (x : ℝ) : ℝ := '+p('x'),'',
           'theorem nonnegative (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :',
           '    0 ≤ polynomial x := by']
    for i,t in enumerate(terms):
        lines.append(f'  have h{i} := squareTerm_nonnegative {t} (by norm_num) x hx hx1')
    lines += ['  have hsum : 0 ≤ '+sum_expr(values)+' := '+proof,
              '  have identity : polynomial x = '+sum_expr(values)+' := by',
              '    dsimp [polynomial, SquareTerm.eval, evalPolynomial]', '    ring',
              '  rw [identity]', '  exact hsum','',
              f'theorem nonzero_value : polynomial {point} ≠ 0 := by',
              '  norm_num [polynomial]','',
              'theorem annihilation : '+sum_expr([f'{real(c)} * {real(y)}' for c,y in zip(coeff,moments)])+' = 0 := by',
              '  norm_num','',
              'theorem finite_supported_bank {A : Type*} [Fintype A]',
              '    (weight value : A → ℝ)',
              '    (hw : ∀ a, 0 ≤ weight a)',
              '    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)']
    for i,(e,y) in enumerate(zip(powers,moments)):
        lines.append(f'    (moment{i} : ∑ a, weight a * (value a)^{e} = {real(y)})')
    lines += ['    (a : A) (ha : 0 < weight a) :',
              '    polynomial (value a) = 0 ∧ value a ∈ Set.Ioc (0 : ℝ) 1 := by',
              '  have zero : ∑ b, weight b * polynomial (value b) = 0 := by',
              '    calc',
              '      _ = ∑ b, '+sum_expr([f'{real(c)} * (weight b * (value b)^{e})' for c,e in zip(coeff,powers)])+' := by',
              '        apply Finset.sum_congr rfl', '        intro b _',
              '        dsimp [polynomial]', '        ring',
              '      _ = '+sum_expr([f'{real(c)} * (∑ b, weight b * (value b)^{e})' for c,e in zip(coeff,powers)])+' := by',
              '        simp only [Finset.sum_add_distrib, Finset.mul_sum]',
              '      _ = 0 := by',
              '        rw ['+', '.join('moment'+str(i) for i in range(len(coeff)))+']',
              '        norm_num',
              '  exact ⟨supported_atom_is_root weight value polynomial hw',
              '    (fun b => nonnegative (value b) (hv b).1.le (hv b).2) zero a ha, hv a⟩','',
              '#print axioms nonnegative','#print axioms nonzero_value',
              '#print axioms annihilation','#print axioms finite_supported_bank','',
              'end Astra.Generated.'+namespace,'']
    return '\n'.join(lines)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate',type=Path)
    p.add_argument('output',type=Path)
    a=p.parse_args()
    from certificates import MAX_BYTES
    with a.certificate.open('rb') as f:
        certificate=loads(f.read(MAX_BYTES+1))
    with a.output.open('x') as f:
        f.write(render(certificate))


if __name__=='__main__':
    main()
