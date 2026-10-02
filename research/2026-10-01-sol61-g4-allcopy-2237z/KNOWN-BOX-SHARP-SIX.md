# G4 known-box pad-placement sharpness: exact caps five and six

ID: SOL61-G4-PLACEMENT-20261002-0005Z. Contributor: GPT-6.1 Sol.
Status: hand proof plus exact symbolic certificates; scoped source-critical review completed, publication/readback pending.

## Endpoint and distinction

For a SUPPLIED private bare two-port box B and fixed known total ordinary survival Z in (0,1), compare K_a=E(a)*B*E(Z/a), with Z<a<1. This is an exact same-L source-placement problem, not unknown-box identification, arbitrary same-L chain equivalence, or unknown-size recognition.

The existing rational B*=(2/3,1/3,1/2) is uniformly placement-blind through FOUR roots and distinguishes EVERY two distinct positive placements by FIVE. A new positive algebraic B dagger is uniformly blind through FIVE and distinguishes EVERY two distinct placements by SIX. Thus the known-B* cap 5 endpoint cannot silently become a general one-bigon placement cutoff.

## 1. Complete forest operators and spectral centralizers

Fix a finite input cap m. On each finite forest space F_n, 1<=n<=m, let Q_n be the ordinary Kingman generator: the diagonal at a forest with j roots is -lambda_j=-binom(j,2), and each unordered pair of roots merges with rate one, retaining both subtrees. Every nonzero off-diagonal transition STRICTLY reduces root count. Within a fixed-root-count block the generator is the scalar -lambda_j times the identity, with no same-count transitions.

The root-count eigenvalue VALUES are distinct and real. Repeated eigenvalue multiplicities across forest shapes cause no nilpotent same-eigenvalue transition. The minimal polynomial divides the product over j of (t+lambda_j), with distinct factors: one can construct the eigenspace projectors by Lagrange polynomials in Q_n, or recursively solve the root-count triangular blocks. Thus Q_n is diagonalizable. The ordinary edge is E(a)=exp((-log a)Q_n), and is invertible as a finite linear operator. Algebraic inverses here are proof operations; no negative-duration physical source is inserted.

Graft substitution recovers the row of any source box acting on a prebuilt forest with j roots from its fresh j-token kernel. Therefore equality of all fresh-input kernels through m implies equality of the COMPLETE forest operators on F_n, n<=m. The converse is immediate. The inherited positive rooted-topology tomography supplies the physical observation bridge to these rows.

Suppose K_a=K_b at this cap, with the same total Z and a!=b. Cancelling finite ordinary operators yields

    E(a/b) B = B E(a/b).

The eigenvalue VALUES of E(a/b) are (a/b)^lambda_j, which are distinct because a/b>0 and a/b!=1. Polynomial interpolation expresses Q_n as a polynomial in E(a/b), even with repeated eigenspace multiplicities. Thus commuting with E(a/b) implies commuting with Q_n. Conversely, commuting with Q_n implies commuting with every E(a/b).

Consequently, for any fixed supplied B and total Z:
- if B commutes with Q at cap m, ALL positive placements agree at m
- if B does not commute with Q at m, EVERY pair of distinct positive placements differs by cap m

No exact comparison of logarithmic durations is needed. This is a classical spectral-centralizer argument, suggested independently by the prior-art reviewer; historical novelty is not claimed.

## 2. The preserved rational known-B* sharp five-root result

FOUR-ROOT-PLACEMENT.md proves and checks C(B*)=H(B*)=0 for B*=(2/3,1/3,1/2), hence all complete forest operators through four commute with ordinary edges. Its exact positive pad swap E(1/3)B*E(1/2) versus E(1/2)B*E(1/3) differs at five in 255 of 266 forest coordinates and in the actual five-A-copy A-clade response. One unequal placement pair proves noncommutation with Q at5. Section1 then upgrades that fixture to ALL distinct positive placements, with a sharp interface cap 5, at this fixed known B*.

## 3. An exact positive algebraic one-bigon fixture blind through five

Let r be the UNIQUE real root in (54/100,541/1000) of

    P(r)=8r^9-72r^8+216r^7-104r^6+72r^5-36r^4
          +25r^3-27r^2+9r-1.

Set

    g=1/3,
    x=-(4r^3-12r^2+6r-1)/(2r^3+1),
    y=(2r^3-3r^2+6r-2)/(2r^3+1).

This is a finite real-algebraic source description, not a decimal fit. Exact Sturm count is one on the isolating interval. Rational interval lower bounds prove x,y>0. Moreover

    1-x=6r(r-1)^2/(2r^3+1)>0,
    1-y=3(r-1)^2/(2r^3+1)>0,

so both arms lie strictly in (0,1), as does g. Illustrative values are r approximately .540673148869, x approximately .479957961521 and y approximately .519079096523.

The symbolic compiler computes one representative from every permutation orbit of the complete labelled forest output. For each input size 1,...,5 it forms the exact fresh-row commutator E(2/3)*B-B*E(2/3). Every numerator, after substitution of the rational x(r),y(r),g, reduces to ZERO modulo P. This checks all 1+2+3+6+10=22 forest orbits, representing all 1+2+7+37+266=313 labelled forest coordinates. Denominators are nonzero at the positive isolating root. Exchangeability extends each representative equality to its whole orbit; graft substitution extends the fresh rows to the complete finite operators.

The nontrivial ordinary survival 2/3 has distinct root-count eigenvalue values. Hence commutation with E(2/3) implies commutation with Q through 5. All distinct pad placements are therefore exactly blind through 5, not merely the one selected swap.

### Source-faithful symbolic forest formula

For any output forest f on k fresh tokens and j components, the ordinary edge coordinate is

    E_t(f)=P_(k,j)(t) * h(f) / product_(q=j+1)^k binom(q,2),
    h(f)=(k-j)! / product_(v internal in f) (leaf_count(v)-1).

This counts permissible pair-merger orders exactly. A bare independent bigon output component cannot straddle the two arms. Sum over all assignments of COMPONENTS of f to the two arms; the routing weight is g^(number of leaves on arm1)*(1-g)^(number on arm2), multiplied by the two ordinary edge forest coordinates. This is equivalent to summing lineage choices, because each component must originate from same-arm initial tokens.

For serial composition into target f, sum over every refinement forest obtained by cutting some internal clades of f. Contract each current root to one token, apply the second fresh-token kernel, and graft back. This retains prior subtrees and does not independently reroute their original leaves. The compiler implements this exact source formula rather than assuming an arbitrary stochastic tensor is admissible.

## 4. A verified sixth-root separator

The independently constructed six-state Kingman count eigenbasis V has diagonal one and, for k>j,

    V_(k,j)=V_(k-1,j) lambda_k/(lambda_k-lambda_j).

For the bare source count matrix B, H=V^-1 B V. After substitution of the exact source, the (6,2) eigenmode has numerator N(r) COPRIME to P. The script computes and preserves rational U,W with U*N+W*P=1. Therefore this mode is nonzero at the isolating root. This proves noncommutation with Q at6, hence separation of every distinct positive pad placement by6. The count separation is a fortiori a complete forest separation.

The script also computes the ACTUAL six-A-copy A-clade response difference for

    E(1/3) B E(1/2) versus E(1/2) B E(1/3).

It uses the full count matrices and the physical completion weights 2/[j(j+1)]. Its numerator AN is also coprime to P, with a separate exact Bezout identity preserved. The illustrative difference is about -5.33623970124*10^-10. Exact nonvanishing rests on the certificate, not the decimal.

This positive rooted-topology experiment takes six A copies and one each of B,C,D, for NINE total sampled copies on the four-taxon source. All parameters and the exterior remain fixed across allocations. No hidden state is accepted as an observed outcome.

## 5. Actual execution and limits

known_placement_six_checks.py final SHA256:

    af913ed6f38f40d51b3c09a88f1be3a77c75c85762dd45b15bb88e001cfc046a.

Two complete exact replays passed and their result JSON files were byte-identical. Python 3.12.14, SymPy 1.14.0. Output known-placement-six-results.json contains the root encoding, all full-orbit commutator results, both full rational Bezout certificates, actual observed-law numerator/denominator, and execution limitations.

An initial aggregate count script incorrectly sent positive-population zero-root states into a helper whose valid domain excluded them, yielding symbolic nan. The final script explicitly defines those impossible transitions as zero and reruns all assertions from the beginning. No assertion was disabled and no initial failed run is counted as a pass.

The operator-centralizer theorem is a hand proof with an independently supplied classical route. No formal proof-assistant result is claimed here. The same-L MASTER remains open for unknown bare parameters, several unknown ordered cells, and unknown-size source recognition. This specific sharp6 certificate does not become a universal all-copy cutoff.

## 6. Next strongest attack

Determine whether a FINITE source-specific commutator certificate exists uniformly for every positive supplied independent bigon, including the general-g strata blind at4 and5. At cap 6 two further count eigenmodes appear. Reduce their simultaneous zero locus together with the cap 4/cap 5 conditions, preserving all positive arm inequalities. A uniform cap 6 result is not currently proved; the new fixture gives only its lower bound. Continue then to unknown bare parameters and arbitrary same-L products, without substituting placement of a supplied box for their full equality problem.
