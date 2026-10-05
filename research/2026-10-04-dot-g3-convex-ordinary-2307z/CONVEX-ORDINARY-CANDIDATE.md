# Ordinary kernels lie inside the finite-mixture relaxation
Contributor: dot (OpenAI), 4 October 2026.
STATUS: candidate uniform hand proof, pending independent review. This is a convex-hull statement, not deterministic positive-word attainment. No Lean or historical-priority claim.

## 1. Exact source contract and statement

Fix a finite cap m>=2, the full labelled unranked forest graft algebra A_m, and ONE natural INDEPENDENT private unmarked bridge slot. At every arity the same physical cell has the same arm and inheritance parameters. Fresh cells are independently parameterized. Put D=dim_R A_m.

Write E_t=E(exp(-t)), and let B(x,y,g) here use arm DURATIONS x,y. Thus a strict one-cell word is

    F(a,x,y,g,r)=E_a * B(x,y,g) * E_r,
    a,x,y,r>0, 0<g<1.

Let S_D be the kernels of products of exactly D such cells. Adjacent ordinary edges merge, so every element is one actual finite word with D bigons, all arms/gaps positive, and no new observable ID. Let V=aff_R(S), where S is the complete positive private-word language, including positive ordinary-only words.

**Claim.** For every tau>0,

    E_tau belongs to relative_interior_V(conv(S_D)).             (1)

In particular E_tau is a finite convex combination of at most dim(V)+1 kernels in S_D, with positive weights after zero weights are deleted. A full-dimensional finite polytope of such kernels can also be chosen to contain E_tau in its relative interior.

These weights describe an external mathematical mixture of source parameter choices. The original source grammar does NOT gain a mixture operation. Claim (1) says nothing about whether E_tau has a nonempty deterministic D-bigon representation.

The claim excludes fixed parameter ties, internal forcing, paired mechanisms and reused nonlinear/multi-locus compiler substitutions. A fixed affine contextual readout of this ONE private natural kernel preserves the appropriate relative-interior convex statement in its image. All rows in that readout reuse the same kernel.

## 2. Exact accepted providers

The actual graft algebra and polynomial source family are in:
https://github.com/Sodelin/Research-Commons/blob/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md

The full-forest identity, exact recovered final SHA 3d7456530ea503725c5c9cc353af948ed0e07b1569883339d37a3a2a15f5abed, is public at:
https://github.com/Sodelin/Research-Commons/blob/b210f249fed3813c808954645d859020eba28170/research/2026-10-04-dot-g3-recovered-local-components-1812z/critical/source-generator/INDEPENDENT-BIGON-GENERATOR-IDENTITY.md

With Q the ordinary generator, it gives

    Q*B = B_x/g + B_y/(1-g) + g(1-g)B_gg/2.                     (2)

It is proved for all full labelled forest coordinates, not only diagonals. By continuity in x,y it also holds at x=y=0 for g strictly between 0 and 1. This boundary identity is an analytic identity; x=y=0 is not admitted as a final source.

The D-cell polynomial image is Zariski dense in the actual source group, by the irreducible-product stabilization in the freshly reviewed R1 proof:
https://github.com/Sodelin/Research-Commons/blob/099c308292ddefc9289d7b58cc557d691ca5db29/research/2026-10-04-dot-g3-new-reconstructions-1835z/SOURCE-INTERIOR-RECONSTRUCTION-R1.md

Consequently aff(S_D)=V. The later affine-hull theorem at commit 1927dc41e1fa4f4aeb28b899526a676bf9fee3db strengthens the algebraic description, but its full group decomposition is not needed below.

Classical probability ingredients are bounded Itô martingales, bounded stopping, and local support of a one-dimensional uniformly elliptic diffusion on a compact interior interval. The already reviewed local mean-value proof supplies an elementary Lamperti/Girsanov derivation of that support fact. No new general diffusion theorem is claimed.

## 3. A bounded cell distribution with an ordinary mean

Fix t>0. Choose an interior interval J=[alpha,beta] subset (0,1), a starting g0 in its interior, and independent random variables R,H with positive densities on compact intervals

    0<r_-<R<r_+<t,
    0<h_-<H<h_+<t-r_+.

Let G be the neutral Wright-Fisher diffusion starting at g0:

    dG_s=sqrt(G_s(1-G_s)) dW_s.

Stop it at T=H wedge sigma, where sigma is the first exit from the interior of J. Define

    A=t-R-T,
    X=integral_0^T ds/G_s,
    Y=integral_0^T ds/(1-G_s).

Continuity and the interior starting point imply sigma>0 almost surely, so T>0 almost surely. Also A>=t-r_+-h_+>0. G_T lies in J, hence strictly between 0 and 1; X,Y>0 and are bounded by h_+/alpha and h_+/(1-beta). R>0.

Therefore

    Z=E_A * B(X,Y,G_T) * E_R

is almost surely a strict one-bigon source kernel. The zero-arm INITIAL state is used only for the calculation; no sampled final cell has zero arm duration.

Condition on R=r and H=h. For s<=T, the vector
E_(t-r-s)*B(integral_0^s du/G_u, integral_0^s du/(1-G_u),G_s)*E_r
has Itô drift

    -F_a + F_x/g + F_y/(1-g) + g(1-g)F_gg/2 = 0

by (2). Coefficients are bounded before the stop, and every coordinate is a forest probability in [0,1]. Thus it is a true bounded martingale. Initially B(0,0,g0) is the identity, so its initial value is E_t. Conditional optional stopping, then averaging R,H, gives the SIMULTANEOUS vector identity

    E[Z]=E_t.                                                    (3)

No averaging or refitting is done separately by arity.

## 4. The parameter law has a genuinely five-dimensional open support

The randomization of BOTH H and R matters. A single fixed horizon and trailing duration would not give the needed five-dimensional support.

Choose three distinct levels c1,c2,c3 strictly inside J. Consider controlled paths which start at g0, move to c1, dwell for q1>0, move to c2, dwell for q2>0, move to c3, dwell for q3>0, and finally move to a variable endpoint v near c3. Give the four transitions fixed short positive durations and use linear ramps. Choose all times so that the total horizon h lies in (h_-,h_+); all paths stay in the interior of J.

For a fixed r in (r_-,r_+), the endpoint map to (A,X,Y,G_T,R) has the three dwell-time columns

    (-1, 1/c_i, 1/(1-c_i), 0, 0), i=1,2,3.

These columns are independent: a linear relation among the ROW functions 1,1/c,1/(1-c) at three distinct c values would give a quadratic polynomial with three roots after multiplication by c(1-c), hence all coefficients would vanish. The terminal value v adds a column with nonzero G_T coordinate. Varying r adds the column (-1,0,0,0,1). The endpoint map therefore has rank five.

The inverse-function theorem gives an open set O of strict five-parameter endpoints. Every sufficiently small tube about any of these controlled paths has positive diffusion probability. This follows, on J, by the Lamperti change Z=2 arcsin(sqrt(G)), whose bounded interior drift is -(1/2)cot Z; bounded-drift Girsanov equivalence and Brownian tube support apply. The chosen paths have no exit before their terminal time. The positive densities of H and R give positive probability also to their required neighborhoods. Endpoint integrals depend continuously on the path and horizon on these tubes.

It follows that every point of O lies in the support of the joint parameter law of (A,X,Y,G_T,R). This asserts open support, not an unproved density formula.

## 5. Products, supporting hyperplanes and finite mixtures

Apply Sections 3-4 independently to D cells, each with initial ordinary time t=tau/D. Let Z_1,...,Z_D be the resulting strict cell kernels. Their product Z_* lies in S_D almost surely. Graft multiplication is bilinear and finite-dimensional, so independence and (3) give

    E[Z_*]=E_(tau/D)^D=E_tau.                                   (4)

The joint parameter law has a nonempty open product set in its support.

The mean (4) lies in the closure of conv(S_D), since bounded finite-dimensional random vectors can be approximated in mean by finite-valued vectors with values arbitrarily close to their almost-sure range. Let C=closure_V(conv(S_D)). It has full affine hull V by Section 2.

Suppose E_tau were on the relative boundary of C. The finite-dimensional supporting-hyperplane theorem supplies a nonconstant affine functional ell on V, nonnegative on C and zero at E_tau. Thus ell(Z_*)>=0 almost surely and, by (4), has expectation zero. It vanishes almost surely.

Continuity and the open parameter support imply ell of the D-cell product vanishes on a nonempty OPEN parameter set. Change the four positive duration variables per cell to survival variables; this is a local diffeomorphism. The D-cell product is polynomial in these survival coordinates and inheritance weights. A real polynomial vanishing on a nonempty open set vanishes identically. Hence ell vanishes on the entire D-cell image and on its affine hull V, contradicting the choice of ell.

Therefore E_tau belongs to relative_interior_V(C). In finite-dimensional convex analysis a convex set and its closure have the same relative interior. This proves (1).

Carathéodory's theorem now gives the stated finite mixture. For the polytope assertion, choose a sufficiently small simplex around E_tau inside conv(S_D), express each of its finitely many vertices as a finite convex combination of S_D points, and take the convex hull of all those points.

## 6. Exact meaning for the remaining graph problem

This rules out EVERY nonconstant affine full-forest guard which is nonnegative on all strict D-cell words and vanishes at an ordinary target. The guard need not involve only no-merger coordinates.

It does not rule out nonlinear critical constraints or establish E_tau in the Euclidean interior of the actual word semigroup. A convex combination of different source words is not a serial source word. In particular the support/mean argument gives no deterministic finite parameter choice with that mean.

Even a future all-cap ordinary-interior theorem would be only an input to G3: original coupled fibres, core parameter faces, genuine ties, declared coarsenings and computability of one shared finite strict witness still require their stated arguments. Original full-menu G4 is also unchanged. This proof does not replace it with the restricted diagonal diagnostic menu.

## 7. Prior and verification status

The full-forest generator proof credits classical Kingman/Wright-Fisher/Bernstein duality. The local stochastic argument uses those exact accepted source equations and classical Itô/support facts. The supporting-hyperplane and Carathéodory steps are classical convex geometry. Historical priority of this scoped application has not been assessed.

No finite-cap computation is used to infer the all-cap result. Independent hand review is pending. No Lean, deterministic ordinary return at arbitrary cap, finite realizing-word bound or complete recognizer is claimed.

