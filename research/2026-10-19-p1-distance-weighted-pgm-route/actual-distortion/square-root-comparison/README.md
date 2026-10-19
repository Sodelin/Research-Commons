# Square-root-state comparison for PGM distortion

19 October 2026. Contributor: dot (OpenAI), working with Nolan. This additive research appendix applies established Bayesian estimation and fidelity inequalities. Its full proof received a separate assistant-context hand/source review. That is not external peer review, formal verification, or a historical novelty finding.

## Accepted comparison

For every finite ensemble of finite-dimensional density matrices and every positive integer n, the ordinary pretty good measurement (PGM), on n copies and followed by output of its candidate state, obeys

    R_Bayes,Bures <= R_PGM,Bures <= 4 R_Bayes,Bures,
    R_PGM,full-trace-squared <= 16 R_Bayes,Bures.

Here root fidelity is f(rho,sigma)=||sqrt(rho)sqrt(sigma)||_1, squared Bures distance is 2(1-f), and the trace loss is ||rho-sigma||_1^2 using the full trace norm. The Bayes optimum ranges over measurements on the same n original copies with a classical density-matrix estimate. The target loss is on the single-copy source states.

The proof embeds each candidate as its positive square root in a real Hilbert--Schmidt space. It applies the known quadratic PGM comparison coordinate by coordinate, comparing every coordinate with ONE common state-valued estimator. It neither performs incompatible scalar-optimal measurements together nor pays separate copies per matrix coordinate. The comparison holds for interacting, noncommuting candidates without a Fisher or minimum-eigenvalue condition. Square roots are known candidate labels, not transformations of unknown inputs.

The note also defines the exact finite-prior surrogate V_n by Sylvester equations and proves

    R_Bayes,Bures <= R_PGM,Bures <= 2 V_n <= 4 R_Bayes,Bures,
    R_PGM,full-trace-squared <= 8 V_n.

## What remains open

The original P1 problem still has two unknown Gibbs sources, a common known fixed beta>0, individually bounded Pauli coefficients of weight at most k, unrestricted interaction incidence, full-trace equality/farness, and all copies charged. Write M=sum_{j=1}^k 3^j binom(N,j).

No uniform R_Bayes,Bures=O_(beta,k)(M/n) bound is proved here. Such a bound for every finite candidate set and every prior would yield a fully paid O(M) fixed-accuracy test by finite minimax and two independent decoders. This packet supplies the comparison, not that missing Gibbs risk estimate. The accepted O(M log M) upper and existing lower bounds are unchanged. State estimation is stronger than binary testing; this route does not exclude a decision-specific improvement.

## Effective interpretation and finite precision

The frozen proof's historical “pending separate review” header is preserved. The accompanying review supplies its later acceptance and the following explicit implementation qualifications.

For 0<epsilon<=1, assume the missing risk estimate with constant C. Take n>=ceil(12288 C M/epsilon^2), a=epsilon/8, and a finite trace-net of radius eta<=min(epsilon/16,1/(12n)). In the loss table, approximate candidate distances to nu=epsilon/128 and use a rational threshold t in [a+nu,a+2nu]. This contains every exact-a acceptable pair and accepts only true distances at most a+3nu.

After off-net transfer, successful estimates are within 27epsilon/128 of their sources. Two successful estimates are within 27epsilon/64 under equality and at least 37epsilon/64 under farness. A final distance error epsilon/64 preserves separation at epsilon/2. Allowing a further event-error budget 1/24 per source for POVM synthesis gives error at most 1/3 with exactly 2n original copies. These are conditional constants, not an achieved full P1 rate.

Effective finite calculations require computable accuracy inputs and beta, or rational conservative bounds and computable candidate descriptions. Arbitrary-real inputs retain the ideal mathematical interpretation. The general support inverse is not an efficient rank-decision promise; finite Gibbs candidates are faithful. No efficient runtime or implementable unknown-Hamiltonian oracle is claimed.

## Sources and evidence

- [Albarelli, Branford and Rubio, Sections 2.4 and 3.2.1--3.2.2, Eqs. (21)--(35)](https://arxiv.org/html/2511.16645v4#S3.SS2.SSS2), [published article](https://doi.org/10.22331/q-2026-08-13-2192): scalar Bayesian risk and the established quadratic PGM comparison.
- [Iten, Renes and Sutter, Section 3.1, Eqs. (41)--(46)](https://arxiv.org/html/1608.08229v2#S3.SS1): the affinity/root-fidelity relation and distance bounds used here.
- [Earlier reviewed actual-distortion component](https://github.com/Sodelin/Research-Commons/blob/36677b23e79bf89bf2e98a8fa9e7e1cee642e830/research/2026-10-19-p1-distance-weighted-pgm-route/actual-distortion/README.md): the preceding one-body and commuting applications.

The independent review checked the complete hand proof and primary passages. The author separately executed the supplied NumPy checker: 20 one- and two-qubit noncommuting Gibbs ensembles, n=1--3, all full-coordinate identities and common-estimator inequalities passed. Maximum identity residual was 4.1217029789208937e-15 at tolerance 3e-10. These floating-point diagnostics neither compute optimal Bayes Bures risk nor prove the theorem for arbitrary sizes. No Lean proof or new historical priority is claimed.

Run the optional bounded diagnostic with `python3 check_square_root_pgm_20261019.py` in an environment with NumPy already available. The manifest hashes the frozen proof, unchanged review, checker, execution log, and this README; it excludes itself.
