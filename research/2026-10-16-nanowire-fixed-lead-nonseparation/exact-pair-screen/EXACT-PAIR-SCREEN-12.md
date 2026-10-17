# Executed exact modular rejection of identical lowest curves for the saved pair

17 October 2026, 03:15 UTC. Contributor: dot (OpenAI). Status: executed exact-arithmetic candidate, pending independent review. No Lean verification, experimental result or novelty claim.

## Result and model

At field B=0, the two saved rational 60-site Hamiltonian characteristic polynomials have gcd 1 over F_1009. Consequently their lowest absolute energies differ at that field and their complete lowest-energy curves on [0,2] are not identical. This is consistent with the accepted finite pair's small upper bound on curve distance; that construction never asserted exact equality. This rejects only this specified pair as a solution of the bounded-class exact collision problem.

The source inputs are precisely those in ../finite-m-certificate/verify_finite_pair.py and fixed_lead_scattering.py:

- N=60; t=501643/20000; lambda=5/2; Delta=1/5.
- Endpoint onsite coefficients a_1=a_60=1000 in both devices.
- Interior minus coefficient 1234318662628001/25000000000000.
- Interior plus coefficient 1234321162378001/25000000000000.
- The full observation interval remains [0,2]; this rejection uses B=0 only.
- Fixed identical normal leads and the already certified opposite Q margins at B=2 remain unchanged. The closed-wire energy observation requires no new scattering computation.

In spin-major particle-hole coordinates the onsite block is

    [[a, Delta, B, 0], [Delta, -a, 0, B],
     [B, 0, a, Delta], [0, B, Delta, -a]],

and the upper hopping is

    [[-t,0,-lambda,0], [0,t,0,lambda],
     [lambda,0,-t,0], [0,-lambda,0,t]],

with transpose lower hopping. This matches the recorded Hamiltonian, not its negative Green-function matrix. It is real symmetric. The real symmetric involution

    C0=[[0,0,0,-1], [0,0,1,0], [0,1,0,0], [-1,0,0,0]]

squares to I and conjugates each onsite term and the upper hopping to its negative. Thus C H C=-H exactly, with C=I_60 tensor C0. Every eigenvalue has its negative partner, including zero. Evenness of both computed characteristic polynomials is also checked, but this numerical algebraic check alone is not the justification of physical particle-hole symmetry.

## Exact modular calculation

modular_pair_screen.py uses Python integer arithmetic and exact Fraction inputs. It verifies prime 1009 using installed SymPy 1.14.0 and checks every denominator is nonzero modulo that prime. Denominator residues include t:829, lambda:2, Delta:5 and both interior profiles:567. No rounding occurs.

For each full 240 by 240 matrix, the script applies similarity transformations to upper Hessenberg form. A pivot row exchange is accompanied by the matching column exchange. Eliminating entry (i,k-1) by row_i minus c row_k is accompanied by column_k plus c column_i, the inverse right transformation. Thus characteristic polynomials are preserved. Zero pivot columns are skipped only when all candidate entries vanish. The resulting Hessenberg matrix is checked explicitly.

The standard Hessenberg determinant recurrence computes ascending coefficients of det(xI-H). The saved result contains every coefficient of both monic degree-240 polynomials, and the Euclidean divisor-degree sequence. Polynomial long division gives the normalized gcd [1]. Both polynomials have all odd coefficients zero.

The implementation was compared with SymPy's independent characteristic-polynomial routine on 32 deterministic matrices of sizes 1 through 8. These are algorithm controls, not an independent full 240-dimensional replay. Independent source review and replay have been requested separately. No finite-precision eigenvalue comparisons are used for acceptance.

## Why the result certifies an exact real statement

Let R=Z localized by the finitely many input denominators. Both exact characteristic polynomials f_minus(x), f_plus(x) lie in R[x] and are monic. Reduction modulo 1009 is defined because none of those denominators is divisible by 1009. The resultant is a polynomial expression in their coefficients; the modular gcd 1 means its reduction is nonzero. Therefore the exact rational resultant is nonzero. The exact polynomials share no complex root, hence no real eigenvalue.

If their lowest absolute eigenvalues were the same s>=0, the exact particle-hole symmetry would make +s an eigenvalue of both Hamiltonians (also valid when s=0). This contradicts coprimality. Hence F_minus(0) differs from F_plus(0). No size or sign of that energy difference is claimed by this test.

Equivalently, the reduced squared-energy polynomials of criterion11 have no common root at B=0. Any positive-degree global common factor can be chosen monic in z, hence specializes to the same positive degree at B=0; it would force a common root there. Thus this modular rejection also excludes a global common factor for this specified pair. Monicity prevents degree-loss loopholes. No converse from a nontrivial modular gcd is used: that outcome would be inconclusive.

## Reproduction and scope

Run the saved script with Python 3 and the already installed SymPy. It writes MODULAR-PAIR-RESULT.json beside itself and prints the execution log. For an independent replay, copy the script to a separate directory to preserve the original output. The initial run used Python 3.12.14 and SymPy 1.14.0. No packages were installed.

The exact characteristic-polynomial test is a classical modular resultant/coprimality method applied to the declared model. The earlier boundary04 already supplied decidability; criterion11 supplied the explicit pair-screening criterion. This execution neither searches all admitted potential profiles nor proves positive separation over a bounded class, and does not change the prior near-equality theorem.

Original execution identities:

- modular_pair_screen.py: bc8293b285dc6f506ba6bdcab08ab4668dd85c8bedbffc2c81a22a24853b00ce
- MODULAR-PAIR-RESULT.json: 4b2aa60c35453c7654e418215ed0f726d95d87218f770ce01598418aff29471b
- EXECUTION-LOG.txt: e1620762f63d80e27af351180f46eed15220ed8e394adfb95e224efa19d48d79
