# Testing total positivity and the surviving chronological information

25 October 2026. dot (OpenAI-assisted research), prepared for Nolan.
Status: hand derivations and primary-source applicability checks; no mathematical runtime or independent review of these deductions. No claim of historical novelty or master closure.

## 1. Spectral count guards fail at every finite cap

In the complete labelled-forest action, order states by merger refinement. A source kernel is triangular; at a forest with r current roots its diagonal is b_r, the probability of no merger on those opaque roots. Hence its eigenvalues with multiplicities, characteristic polynomial, determinant, and traces of powers are determined by the finite tuple (b_2,...,b_m) at cap m. This does not assert that its eigenvectors or full matrix are determined by that tuple.

The accepted uniform-time ordinary DIAGONAL-return theorem states that for every m and q in (0,1), an actual nonempty strict finite word has b_r=q^choose(r,2) through m. The construction permits arbitrarily small total pair hazard before positive ordinary padding. For a fixed H>0 and any integer L, apply it with q=exp(-H/L) and concatenate L such words. The endpoint has precisely the ordinary diagonals at H, but at least L genuine hybrid cells. All parameters are shared across arities within each finite rival.

Thus no finite panel composed only of these spectral/diagonal diagnostics, even with arbitrary deterministic postprocessing, bounds actual cell count at the fixed ordinary target. This is an application of the accepted all-cap DIAGONAL theorem, not a new full-forest return or an exact rival for the original rich panel. Its lawful binary coarsened observation implementation is already supplied by the provider.

Provider: https://github.com/Sodelin/Research-Commons/blob/608f690fd76e216036ed2cd282c236fd0aa4ac46/research/2026-10-04-dot-g3-structure-followons-2200z/uniform-diagonal/UNIFORM-TIME-DIAGONAL-FINAL.md

## 2. Ordinary full-forest kernels are not totally nonnegative in any fixed state order

Here totally nonnegative (TN) means every minor is nonnegative in one specified order of the probability-state basis. It does not mean entrywise nonnegative.

Let Q be the actual ordinary Kingman generator on complete labelled forests through at least three roots. At the state consisting of three singleton labels, three different pair mergers lead to three different forest states, each at rate one. In any linear ordering of all states, at least one of those three successor indices j is not adjacent to the source index i.

Write P(t)=exp(tQ)=I+tQ+O(t^2). If j>i+1, put k=i+1 and use rows (i,k), columns (k,j). Its determinant is

    P_ik P_kj - P_ij P_kk = -t Q_ij + O(t^2).

If j<i-1, put k=j+1 and use rows (k,i), columns (j,k). Its determinant is

    P_kj P_ik - P_kk P_ij = -t Q_ij + O(t^2).

In either case it is negative for all sufficiently small positive t. Therefore no fixed permutation of the complete labelled probability-state basis makes EVERY positive ordinary population kernel TN. This already fails before adding hybrids.

This is the elementary necessity underlying classical tridiagonal-generator criteria for totally nonnegative differential systems, not a new general matrix theorem. It rules out a direct import of the standard ordered-state TN/variation-diminishing semigroup theorem into the full forest action. It does not rule out a source-faithful quotient, a different cone, selected minors, or signed changes of basis. Those alternatives require their own proof and must retain the needed whole-law information. Diagonalizing Q in a signed basis does not by itself establish a positive source cone for the hybrid operators.

Primary reference: Binyamin Schwarz, *Totally positive differential systems*, Pacific Journal of Mathematics 32 (1970), 203–229: https://msp.org/pjm/1970/32-1/pjm-v32-n1-p20-s.pdf . The explicit minor argument above is self-contained.

## 3. Exact all-diagonal collision showing what chronology retains

The next structural check uses actual positive source factors rather than an arbitrary matrix counterexample.

Let Q_infty denote ordinary infinite ancestral completion, E_a an ordinary population of exposure a>0, and B_s one fair equal-arm bigon whose two arm survivals are s in (0,1). Let beta be the probability of the specified completed balanced topology ((1,2),(3,4)) on four labels. Ordinary completion has beta(Q_infty)=1/9. Direct enumeration of the first fair routing allocation gives

    beta(B_s Q_infty)=1/9+(1-s)^3/36.                 (1)

Here is the full hand calculation. All four roots in one arm have total probability 1/8 and contribute 1/72. The four 3+1 partitions have total probability 1/2; conditional on any one of them the required topology has probability s/6-s^3/18. The matching 2+2 partition has probability 1/8 and conditional contribution 1-4s/3+4s^2/9; the two crossing 2+2 partitions each have probability 1/8 and conditional contribution s^2/9. Their sum is (5-3s+3s^2-s^3)/36, proving (1).

On at most three fresh roots, any exchangeable completed binary tree law equals the ordinary topology law. Therefore, in E_a B_s Q_infty, any ordinary merger before B_s leaves a continuation on at most three roots and introduces no deviation from ordinary completion. Only the no-merger event on all four roots contributes the deviation. Thus, with d=(1-s)^3/36,

    beta(E_a B_s Q_infty)=1/9+exp(-6a)d,
    beta(B_s E_a Q_infty)=1/9+d.                     (2)

To keep both words within the strict padded grammar, take c,d0>0 and compare

    W_left = E_(c+a) B_s E_d0,
    W_right = E_c B_s E_(a+d0).

They have exactly the SAME no-merger diagonal at EVERY arity, since those scalar factors commute. Their complete four-root finished topology probabilities differ by

    beta(W_right Q_infty)-beta(W_left Q_infty)
        = exp(-6c)(1-exp(-6a))(1-s)^3/36 > 0.       (3)

For c=a=d0=log 2 and s=1/2, (3) equals 7/131072 exactly. This is an algebraic hand value, not an executed numerical test. These are strictly positive actual source words, and they can be inserted in an unchanged eligible untied pendant wrapper. Single-taxon completed topology laws are legal marginals by padding and pruning original taxa.

Consequently, even the ENTIRE diagonal hierarchy loses chronology. Spectral uniqueness cannot be upgraded to full-law uniqueness. Equation (3) is not an unbounded-count example: both sources have one bigon. Its role is to show exactly which information must survive a proposed quotient or variation-diminishing representation.

## 4. Testing a chronological positive charge: exact signed cocycle

There is an exact all-word formula for the balanced-four defect, so its sign can be tested without a numerical ladder. For any actual exchangeable completed continuation U, write D(U)=beta(U)-1/9. For any finite prefix A, opacity and the universal completed laws on at most three current roots imply

    D(AU)=D(A Q_infty)+b_4(A)D(U).                  (4)

Only the singleton-output forest of A calls U on four roots; all other outputs call it on at most three. This proves (4) directly, including arbitrary already formed subtrees. Thus for a word of source factors A_1...A_l,

    D(A_1...A_l Q_infty)
       = sum_i [product_(j<i) b_4(A_j)] D(A_i Q_infty). (5)

These are true PREFIX transports for this completed scalar, not the suffix transports of the different normalized projective residual layer. Ordinary factors have zero charge and positive attenuation.

For a fair unequal-arm cell B_(x,y), the same routing enumeration as Section 3 gives

    D(B_(x,y) Q_infty)
       = [2-3(x+y)+6xy-x^3-y^3]/72.                (6)

This charge has both signs on STRICT physical cells. Equal arms give the positive value in (1). At x=1/4,y=3/4 it equals -5/1152. More strongly, choose

    x=(1+1/sqrt(6))/2,  y=(1-1/sqrt(6))/2.

Then x+y=1, xy=5/24, x^3+y^3=3/8. The actual cell has b_2=3/4 and b_3=27/64=b_2^3, hence ordinary no-merger diagonals through cap three, but (6) equals -1/576. All arm survivals are strictly between zero and one. These values are hand algebra, not executed checks.

Consequently (5) is not a nonnegative per-cell expenditure from which actual count can be bounded. Strict positivity of the source does not make this chronological defect positive. This does not establish full-cap cancellation: other coordinates and the shared tuple remain coupled. It identifies the exact failure of the next natural positive-charge argument after abandoning spectral invariants. The balanced coordinate and affine composition law may overlap inherited cap-four coordinates; no novelty is claimed.

## 5. Master-facing consequence and remaining route

The direct diagonal/spectral route is defeated by exact source examples, and ordinary full-forest TN fails in the probability basis. An actual count certificate must therefore exploit off-diagonal chronological constraints or a different positive algebra that provably retains them.

The balanced coordinate in (1) is not offered as that certificate. General unequal-arm/bias configurations and accepted complete cap-four/five returns prevent extending its one-cell positivity to an arbitrary-word no-return theorem. Standard variation-diminishing theorems supply inequalities only after their required order/cone has been established; an arbitrary sign convention cannot provide that missing source property.

The next unresolved structural route is a source-faithful chronological invariant on the EXACT fixed-target fibre, not the spectrum alone. No such all-positive, arbitrary-length invariant is proved here. Nor is there a family matching increasing COMPLETE caps at one fixed target. Original G4 remains open, and split-only SF remains separately owned.

## Scope and attribution

All source examples use the original strict UNTIED natural pendant-word class, positive ordinary intervals, interior coins, opaque current-root grafting, and one shared physical tuple per source. No controlled replacement IDs, external random parameter mixtures, or new observations are introduced. The diagonal-return theorem and ordinary coalescent laws are inherited. The applications and exact calculations here are scoped hand checks, not a claim that these facts were previously unknown in the archive or literature.
