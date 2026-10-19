# Proposed measurement extension: spectral parity with certified leakage

19 October 2026. Attributed research feasibility checkpoint by dot (OpenAI), working with Nolan.

## Current status and decision

PROPOSED MEASUREMENT EXTENSION, pending Nolan’s approval to adopt the richer observation contract. The original research scope and ownership remain unchanged. This is a conditional mathematical certificate, with no measured-device data or operational guarantee. Historical novelty is unresolved.

The proposal adds the complete ordered Andreev-reflection eigenvalue spectrum, with simultaneous error intervals and all channel multiplicities, plus a certified same-energy reflection-defect bound smaller than one. It does not assume that ordinary local/nonlocal charge conductance supplies these inputs. A justified spectral acquisition method and its full uncertainty budget remain missing.

If these inputs are available, the proof below certifies the sign of the real reflection determinant by a threshold count, including cases where aggregate charge conductance alone is ambiguous. This may justify studying acquisition feasibility; it does not replace the original measurement question.

## Coordinating manual review receipt

On 19 October 2026, the coordinating dot independently read the complete candidate and the primary Beenakker–Dahlhaus–Wimmer–Akhmerov paper, Sections II and III.1, equations (7)–(12). Scoped hand-proof PASS covers preservation of canonical particle-hole symmetry and determinant sign under polar decomposition, the defect and singular-value perturbation bounds, threshold parity, determinant magnitude, and the four-channel attenuated example and its conductance calculation. This is manual mathematical review, with no numerical execution, formal verification, or exhaustive historical-priority audit. Attribution to Béri and the cited class-D scattering literature is retained.

Original candidate SHA256: dfdb253cf62ed6f125529bed778c579f35cc6b599696c4d40c96909ae7808b55. Its text follows unchanged, including its historical pre-review status. This receipt supplies the current review status.

Scope baseline: https://github.com/Sodelin/Research-Commons/blob/d15ec7f5d9a741ecbaa21d8f5f0cca49da4d0b81/research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md

---

# Feasibility: reflection-sign certification from resolved Andreev spectrum and leakage

19 October 2026, 18:23 UTC. Contributor: dot (OpenAI), working with Nolan.

Status: complete elementary hand argument submitted for review. This is a proposed richer measurement contract, not adoption of a replacement for the original conductance menu, a measured-device result, or G4 progress. No historical novelty, execution or Lean claim. Root authorized feasibility analysis only. The repository head checked during this pass was d15ec7f5d9a741ecbaa21d8f5f0cca49da4d0b81.

## Decision-relevant result

If a zero-energy particle-hole-symmetric reflection matrix is certified close to unitary through its leakage, then its determinant sign can be certified from the parity of a resolved Andreev singular-value count across a noise-cleared threshold. This applies uniformly to all matrices satisfying the stated contract. Aggregate charge conductance does not provide the required spectrum or leakage norm. The mathematical proof supplies a possible conditional identification adapter; acquisition of its inputs and admission of a physical device are separate unresolved obligations.

## 1. Exact contract

Let N>=1 be finite and known. In the declared electron/hole channel ordering, let r be a complex 2N by 2N matrix with

    r = J conjugate(r) J,    J = [[0,I_N],[I_N,0]],
    r* r <= I,             ||I-r* r||_op <= d < 1.             (1)

Here * is conjugate transpose. The target is the real reflection determinant Q=det(r), specifically its sign. No statement equating that finite-device indicator to protected operation is assumed.

Let B=r_he and let s_1>=...>=s_N>=0 be its singular values. Their squares R_i are the Andreev-reflection eigenvalues, the eigenvalues of B*B. They are NOT generally the individual entries |B_ab|^2 or merely diagonal entries of B*B in an arbitrary incident-channel basis.

The proposed input is a simultaneous certified enclosure

    l_i <= s_i <= u_i,   0<=l_i<=u_i<=1, i=1,...,N,           (2)

with correct order/multiplicity and no omitted channels, together with the independent bound d in (1). Set

    e = 1-sqrt(1-d).

Suppose there exists a threshold x strictly between 0 and 1 such that each index is decisively classified by one of

    u_i+e < x,                    l_i-e > x.                 (3)

Let m be the number of indices in the second category. Then

    sign Q = (-1)^m,      |Q| >= (1-d)^N.                    (4)

In particular, odd m certifies Q<=-(1-d)^N and even m certifies Q>=(1-d)^N. If (3) fails, this rule abstains. Failure of this sufficient rule does not establish information-theoretic ambiguity.

For measured sorted probabilities R_i in certified intervals [a_i,b_i] contained in [0,1], take l_i=sqrt(a_i), u_i=sqrt(b_i). An operator-norm enclosure of B*B also supplies ordered eigenvalue intervals by the Hermitian min-max inequality. The confidence level, if the bounds are statistical rather than deterministic, must cover all input bounds jointly. The theorem then holds on that simultaneous event; no statistical acquisition guarantee is supplied here.

## 2. Primary unitary supplier and its exact role

Beenakker, Dahlhaus, Wimmer and Akhmerov, Random-matrix theory of Andreev reflection from a topological superconductor, Phys. Rev. B 83, 085413 (2011), arXiv:1012.0932v3:

https://arxiv.org/html/1012.0932v3
https://arxiv.org/pdf/1012.0932

Directly inspected Section II and Section III.A. The HTML equations (7)-(12) give class-D unitary polar blocks, including both channel parities and determinant signs. Nonendpoint Andreev eigenvalues have even multiplicity (Béri degeneracy), while the parity of the number at one equals the determinant sign. Thus for ANY unitary canonical-PHS U, and any x in (0,1) outside the singular spectrum of U_he,

    det U = (-1)^{ number of singular values of U_he above x }.

This is a deterministic consequence of the block decomposition; no random-matrix distribution or typical-source assumption is needed. Endpoint or coincident degeneracies are allowed. Paired blocks contribute even counts; the unpaired perfect-Andreev block contributes determinant -1. The paper credits Béri for the degeneracy. We retain that attribution rather than treating spectral parity as new.

The unitary theorem cannot be applied directly to the lossy r in (1). The polar correction below is essential. The paper's low-temperature transport interpretation does not by itself establish acquisition of the complete spectrum for a real device. The focused search found no exact match for the present robust lossy formulation, but that is not a novelty or exhaustive-prior conclusion.

## 3. Proof of the lossy/noisy transfer

Equation (1) implies sqrt(1-d)<=sigma_min(r)<=sigma_max(r)<=1. Hence r is invertible. Put

    P=(r*r)^(1/2),       U=r P^(-1).

U is unitary. The map C(X)=J conjugate(X)J preserves multiplication, adjoints, positivity and real continuous functional calculus. Since C(r)=r, it fixes r*r, P, P^(-1), and U. Thus U has the same canonical PHS symmetry. Also det r is real by PHS, det P is strictly positive, and

    sign(det r)=det U in {-1,+1}.

By the singular-value decomposition,

    ||r-U||_op = ||P-I||_op = 1-sigma_min(r) <= e.             (5)

Compressing to the he block cannot increase operator norm, so ||r_he-U_he||<=e. The singular-value min-max inequality gives

    |s_i(r_he)-s_i(U_he)| <= e   for every ordered index i.    (6)

For completeness, this inequality follows from the variational characterization of ordered singular values: on every candidate subspace, ||Av||<=||Bv||+||A-B|| for unit v; applying the min-max formula and interchanging A,B proves both directions. No matching of singular vectors is assumed.

Equations (2)-(3) therefore place exactly m singular values of U_he above x and the rest below. The primary unitary parity theorem gives (4)'s sign. Finally |det r| is the product of its 2N singular values, each at least sqrt(1-d), giving its magnitude bound. This proof neither sets r equal to U nor requires U to be realizable by the original microscopic wire.

Strict separation in (3) excludes threshold equality. d=0 is allowed and recovers unitary reflection; d=1 is excluded because r may be singular and its sign undefined. Very large d may make this sufficient certificate vacuous. A measured interval inconsistent with [0,1] should be intersected with the physical range only when the original error interval contains an admitted value; an empty intersection signals inconsistency, not a sign certificate.

## 4. What leakage input could mean

If r is the reflection block of a common unitary scattering matrix with all outgoing nonreflection channels retained in a block t, then

    r*r+t*t=I,     ||I-r*r||=||t||^2.

A certified upper bound on the largest total-quasiparticle transmission eigenvalue therefore supplies d. A bound Tr(t*t)<=d also suffices, although it may be loose. These include electron AND hole input columns. Under canonical zero-energy PHS the two column-sector traces agree, so twice the electron-input total quasiparticle leakage is a safe full-trace bound.

Signed nonlocal charge conductance is a difference of electron and hole probabilities; it does not supply this sum or operator norm. If there are additional dissipative or unobserved outgoing channels, they must be included in the defect bound; ordinary measured terminal transmission alone cannot silently account for them. Neither a normal-state calibration nor a finite-temperature conductance fit is substituted for the same-device, same-energy bounds in (1)-(2).

## 5. An explicit informative algebraic control

This example checks that the richer conditional rule can distinguish cases left ambiguous by aggregate charge conductance. It is an abstract scattering-class construction, not a new pair in the fixed 60-site Rashba class.

For y in [0,1], define A_y=sqrt(1-y) sigma_x, B_y=sqrt(y) sigma_z and

    U_y=[[A_y,B_y],[B_y,A_y]].

The real Pauli matrices anticommute, so U_y is unitary, canonical PHS, and det U_y=+1. Its two Andreev eigenvalues are (y,y). Use PHS-compatible channel direct sums, retaining electron/hole ordering. Let

    a=(1+1/sqrt(2))/2,  b=(1-1/sqrt(2))/2,
    U_plus=U_a direct_sum U_b,
    U_minus=tau_x direct_sum I_2 direct_sum U_(1/2).

Both have N=4. Their Andreev spectra are (a,a,b,b) and (1,1/2,1/2,0), and determinant signs + and -, respectively. Take r_plus=(99/100)U_plus and r_minus=(99/100)U_minus. Both satisfy (1) with d=199/10000 and e=1/100; their determinant magnitudes are (99/100)^8. Their charge conductances are both

    g=N-||r_ee||_F^2+||r_he||_F^2=4.

Their Andreev probability spectra are scaled by 9801/10000. Suppose those ordered probabilities have absolute error at most 1/1000 each. Threshold x=17/20 works for (3): the two relevant squared comparison levels are

    (x-e)^2=441/625,       (x+e)^2=1849/2500.

For the plus case, a>4/5 and b<1/5, so even after the stated probability error its two high values exceed 1849/2500 and two low values are below 441/625. For the minus case, the value 9801/10000 exceeds the upper level after error; the half-values 9801/20000 and zero are below the lower level after error. Thus the rule certifies even count two for plus and odd count one for minus. All comparisons have strict rational slack after using a>4/5, b<1/5.

This example uses preexisting unitary blocks and classical attenuation; its conceptual content is a richer-observation demonstration, not a claim of a new physical phenomenon. The same scalar charge-conductance observation and the same leakage cannot distinguish this pair. Acquisition of the full resolved spectrum is the extra assumption that does the work.

## 6. Scope and next decision

The mathematical feasibility argument is complete conditional on the established unitary polar-block theorem. It uses classical polar decomposition and singular-value perturbation. It gives no full solution of original finite-temperature aggregate-conductance identification, no measured data, and no protected-operation guarantee.

The input menu is materially stronger than the original local/nonlocal charge-conductance menu. Individual channel probabilities do not automatically recover B*B's spectrum because coherent channel cross terms may matter. A real proposal needs an independently justified spectral acquisition procedure (or full matrix tomography sufficient for it), simultaneous uncertainty bounds, all-channel counting, a certified same-energy leakage bound and physical PHS admission. Thermal convolution, energy dependence, uncertain symmetry and Hamiltonian drift require separate adapters; none is assumed away in an application claim.

Parent should decide whether this richer-observation direction is useful enough to propose to Nolan. Until that decision, it remains feasibility work only. No original scope, ownership or Google Doc is changed. Historical novelty remains unassessed; primary attribution is to Béri and the cited class-D scattering literature. No numerical or symbolic execution was required by this hand proof.
