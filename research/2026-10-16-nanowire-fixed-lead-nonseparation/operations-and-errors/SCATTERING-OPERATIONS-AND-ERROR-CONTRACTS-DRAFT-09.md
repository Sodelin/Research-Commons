# Scattering matrices: valid operations, error bounds and physical limits

17 October 2026, 02:16 UTC. dot (OpenAI), working with Nolan.

**Status: source-led mathematical draft for independent review.** This is groundwork for a reusable module, not an implemented toolkit, a new universal device theory, a Lean certificate or a novelty claim. The operations are classical matrix and network theory. The contribution sought here is an explicit, source-faithful collection of contracts that can be checked before using the accepted conductance bounds.

## 1. What the common framework would contain

Keep three levels distinct:

1. **Matrix statements.** Dimensions, particle-hole symmetry, contraction, invertibility and numerical error are precise mathematical properties.
2. **Transport interpretation.** A reflection block, transmission block and connected network have different input/output meanings. Current polarity, energy, temperature and contact normalization must be supplied.
3. **Physical admission.** One device model, geometry and shared parameter tuple must generate all its blocks and measurement settings. An abstract matrix extremizer is not automatically a realizable member of that model.

The established all-channel determinant theorem uses the first level plus a particular readout formula. It does not require a named wire length or geometry. This makes its conclusion available at any length or geometry that supplies those hypotheses; it does not prove that every abstract attainable pair occurs at every length or geometry.

All dimensions below are finite. All matrix norms without a subscript are the operator norm induced by the Euclidean vector norm. The Frobenius norm is written ‖·‖F. Error allowances are nonnegative. No approximate symmetry is silently substituted for exact symmetry.

## 2. The real matrix algebra behind particle-hole symmetry

For m outgoing and n incoming electron channels, with their hole partners, define

    J_n = [[0,I_n],[I_n,0]],
    PHS(m,n) = {X in C^(2m×2n) : X = J_m conj(X) J_n}.

Equivalently X=[[A,B],[conj(B),conj(A)]], with A,B of size m×n. Let

    U_n = (1/√2) [[I_n,I_n],[−iI_n,iI_n]].

**Lemma 1.** X is in PHS(m,n) if and only if M=U_m X U_n† is real. This transformation preserves operator/Frobenius norms, products of compatible maps and adjoints. When m=n it preserves the determinant.

**Proof.** U_n is unitary and conj(U_n)=U_n J_n, while U_n^T=J_n U_n†. Thus

    conj(M)=U_m J_m conj(X) J_n U_n†.

This equals M exactly under the displayed PHS relation. Conversely, reverse the unitary changes of coordinates. Norm preservation and product/adjoint identities follow from unitarity; square determinant preservation follows from det(U_n)det(U_n†)=1. ∎

Consequently PHS(n,n) is a real unital *-algebra isomorphic to M_(2n)(R): it is closed under addition, real scalar multiplication, multiplication and adjoint. It is not a complex-linear algebra: I is PHS but iI is not.

This Majorana representation is established prior. Beenakker's review gives the basis conversion and the real scattering relation at zero energy. We use a harmless sign variant of its second Majorana-coordinate block; our convention agrees with the accepted all-channel proof. [Beenakker, arXiv:1407.2131v3, Eqs. (21), (41), (63)](https://arxiv.org/pdf/1407.2131v3).

At nonzero energy the physical symmetry generally relates S(E) to conj(S(−E)), rather than making S(E) individually real in the Majorana basis. This draft's real-algebra assertions are zero-energy assertions.

## 3. Passive contractions: closure and nonclosure

Let C(m,n) be the PHS matrices with ‖X‖≤1. Equivalently X†X≤I. This is the admitted passive-amplitude condition; it is not a statement that every such matrix has a particular microscopic realization.

**Lemma 2.** The following operations preserve the indicated contraction class:

- Compatible products: X in C(l,m), Y in C(m,n) imply XY in C(l,n).
- Adjoint: X in C(m,n) implies X† in C(n,m).
- Direct sums, with the fixed permutation that groups electron channels together and hole channels together.
- Real convex combinations of matrices with the same dimensions: 0≤a≤1 gives aX+(1−a)Y in C(m,n).
- Real scalar factors a with |a|≤1.
- Selection of complete electron/hole channel pairs: if E_in and E_out are PHS-compatible isometric embeddings of chosen channel spaces, E_out† X E_in is a PHS contraction.

**Proof.** PHS follows either by the defining relation or the real-coordinate form. Product contraction follows from submultiplicativity; adjoints have the same norm; direct-sum norm is the maximum; convexity and scaling follow from the triangle inequality; the embeddings and their adjoints have norm one. ∎

The contraction class is not itself a linear algebra: I+I=2I fails contraction, as does multiplication of I by any real scalar of absolute value greater than one. Arbitrarily cutting out an electron-only block also need not leave a PHS matrix.

Convex mixing of amplitudes is not the same as a random mixture of devices. For one electron channel, X=I_2 and Y=−I_2 both have g=0 and Q=1. Their amplitude midpoint is zero, with g=1 and Q=0. A classical 50:50 mixture of their measured conductances instead still has g=0. Therefore matrix convexity is not permission to average physical devices or their observations interchangeably.

### Inverse maps require a stronger premise

**Lemma 3.** If a square PHS matrix X is invertible, X^−1 is PHS. If X is also contractive, then X^−1 is contractive if and only if X is unitary.

**Proof.** Inversion preserves the defining PHS identity, or equivalently real matrices remain real under inversion. If both norms are at most one, then for every vector v,

    ‖Xv‖≤‖v‖=‖X^−1 Xv‖≤‖Xv‖.

Thus X preserves every norm, so X†X=I, and a finite square isometry is unitary. The converse follows from X^−1=X†. ∎

An attenuator X=aI with 0<a<1 therefore has an inverse with norm 1/a>1. Its mathematical inverse is not an admitted passive scattering operation. Inverting a fitted response is also not a proof that an inverse physical device can be built.

## 4. Blocks from one device must fit together

For a loss-free two-terminal scattering matrix, in terminal blocks,

    S = [[r,t′],[t,r′]],  S†S=SS†=I.

Its blocks are contractions, but they are not freely assignable. For example,

    r†r+t†t=I,    r†t′+t†r′=0.

Additional unobserved passive channels replace the first equality for the observed blocks by an inequality. Taking r=t=I satisfies separate contraction tests but violates the shared incoming-column condition. A reusable module must retain the common parent scattering matrix or a proved compatible completion, as well as the shared microscopic source when making a device claim.

For square reflection blocks, the accepted readout is

    g=N−‖r_ee‖F²+‖r_he‖F²,  Q=det(r).

For square transmission blocks with equal channel counts, the checked additional readout is

    c=‖t_he‖F²−‖t_ee‖F²,  d=det(t),  g_t=N+c.

Here c uses terminal current positive from the outgoing normal terminal into the device. The transmission determinant is a different quantity from Q and is not thereby a topological invariant. A rectangular transmission block remains a valid amplitude map but has no ordinary determinant.

The full block definitions and opposite published current convention are given in [Rosdahl et al., Physical Review B 97, 045421 (2018), Eqs. (3)–(5), article page 045421-3](https://pure.tudelft.nl/ws/portalfiles/portal/46877558/PhysRevB.97.045421.pdf). The [reviewed transmission corollary](https://github.com/Sodelin/Research-Commons/blob/11797fe733489a74ef1ad71696ded0fdc1e225bb/research/2026-10-16-nanowire-fixed-lead-nonseparation/indicator-register/TRANSMISSION-COROLLARY-INDEPENDENT-CHECK-20261017.md) fixes the conversion explicitly.

## 5. Connecting devices involves feedback, not ordinary multiplication

Ordinary XY is a valid composition of abstract amplitude maps. It is not generally the scattering matrix obtained by connecting two devices, because waves can return through the connection repeatedly. The correct network operation retains those internal amplitudes.

Use external input/output a,b and internal input/output u,v, each with matching finite channel spaces. Write

    [b;v] = S[a;u],   S=[[A,B],[C,D]],   u=Kv.

Assume S and K are contractions and are PHS in the compatible external/internal channel convention. Assume I−KD is invertible. Then

    u=(I−KD)^−1 KCa,
    b=Fa,   F=A+B(I−KD)^−1KC.                         (1)

**Lemma 4.** F is a PHS contraction. If S and K are unitary and the external map is square, F is unitary.

**Proof.** Solving the internal equation gives (1). PHS is preserved by its sums, products and the admitted inverse. For every external input a and its unique internal solution,

    ‖b‖²+‖v‖² ≤ ‖a‖²+‖u‖² ≤ ‖a‖²+‖v‖².

Cancel the internal term to obtain ‖Fa‖≤‖a‖. If S,K are unitary, both inequalities are equalities; a square F then preserves all norms and is unitary. ∎

Taking a direct sum of component scattering matrices and letting K route their connected ports gives the usual regular feedback/star-product construction. The port routing, energy, amplitude normalization and any propagation phases are part of the input; they cannot be dropped merely because dimensions match.

**Prior and singular cases.** This is established Redheffer/network theory, presented with an elementary passive-energy proof. Kostrykin–Schrader's generalized star product treats broader singular unitary cases; their Theorem 3.8 preserves unitarity. Cervera–van der Schaft–Baños, Section 4.2 and Proposition 16, explicitly connect matching wave-variable interconnections to the Redheffer product. Our invertibility condition is a sufficient domain for formula (1), not a claim that every singular feedback network is physically undefined. Dark internal modes may require a separate compatible generalized construction.

- [Kostrykin–Schrader, arXiv:math-ph/0008022v1, Sections 3–4 and Theorem 3.8](https://arxiv.org/pdf/math-ph/0008022v1).
- [Cervera–van der Schaft–Baños, Automatica 43 (2007), Section 4.2 and Proposition 16](https://www.math.rug.nl/~arjan/DownloadPublicaties/CerveraVanderSchaftBanosrev.pdf).

The feedback algebra does not by itself prove that a given lithographic or microscopic connection is represented by these ports. Pointwise zero-energy well-posedness is also not an entire frequency-dependent causality/stability proof.

## 6. Explicit operation-error bounds

These bounds concern errors in admitted matrices, not an automatically inferred measurement or fabrication tolerance.

### Products, sums and adjoints

For contractions X,Y,X′,Y′ of compatible dimensions, with ‖X−X′‖≤ε_X and ‖Y−Y′‖≤ε_Y,

    ‖XY−X′Y′‖≤ε_X+ε_Y.                              (2)

Indeed XY−X′Y′=(X−X′)Y+X′(Y−Y′). Repeated products have error at most the sum of the individual bounds. Adjoints preserve the error; direct-sum error is the maximum; a fixed real convex combination has error at most the corresponding weighted sum.

### Inverses

For invertible X,Y,

    X^−1−Y^−1=X^−1(Y−X)Y^−1,
    ‖X^−1−Y^−1‖≤‖X^−1‖ ‖Y^−1‖ ‖X−Y‖.             (3)

If the smallest singular values are at least δ_X,δ_Y>0, the coefficient is at most 1/(δ_X δ_Y). Without such a bound inversion can amplify errors without a uniform limit. These inverse matrices need not be contractions.

### Regular feedback

Compare (S,K) and (S′,K′), each satisfying Lemma 4. Let ε=‖S−S′‖, ζ=‖K−K′‖ and

    R=(I−KD)^−1, R′=(I−K′D′)^−1,
    ‖R‖≤κ, ‖R′‖≤κ′.

All individual blocks of S,S′ have norm at most one; their differences have norm at most ε. The resolvent identity gives

    ‖R−R′‖≤κκ′(ε+ζ).

Expanding A+BRKC minus A′+B′R′K′C′ one factor at a time therefore gives

    ‖F−F′‖ ≤ (1+κ+κ′+κκ′)ε + (κ′+κκ′)ζ.           (4)

For example, the five terms are A−A′, (B−B′)RKC, B′(R−R′)KC, B′R′(K−K′)C and B′R′K′(C−C′). This proves (4) without assuming commutation. A common bound κ,κ′≤L yields

    ‖F−F′‖≤(1+L)² ε + L(1+L)ζ.

Useful sufficient guards are ‖KD‖≤ρ<1, which gives κ≤1/(1−ρ), or a certified smallest singular value of I−KD. If κ(ε+ζ)<1, the perturbation lemma already certifies invertibility of I−K′D′ and κ′≤κ/[1−κ(ε+ζ)], provided the stated block perturbation bounds hold. Separate passivity and PHS checks are still required for S′ and K′.

### Why passivity alone does not give a uniform feedback-error constant

For 0<ε<1, let a=1−ε, s=√(1−a²) and use the real orthogonal two-port matrix

    S_a=[[a,s],[s,−a]].

With scalar feedback k, formula (1) gives F(k)=(a+k)/(1+ak). Both k=−1 and k′=−1+ε are contractions and both denominators are positive: ε and 2ε−ε². Yet

    |k−k′|=ε,  F(k)=−1,  F(k′)=0.

Thus arbitrarily small connection changes can give an order-one external-amplitude change within the regular passive class. Tensoring the blocks with I_2 realizes the same example in compatible finite PHS channel spaces. This is a conditioning illustration, not a newly claimed nanowire mechanism. It does not contradict a separately controlled resolvent bound, or the generalized star-product results with their own parameter-dependent estimates.

## 7. Converting matrix error into readout and sign bounds

Let X,Y be contractions of equal dimensions, ‖X−Y‖≤ε. Let E embed the n incoming electron coordinates, and let Z_out=diag(I_m,−I_m) be the outgoing charge-sign matrix. Define

    q(X)=Tr[(XE)† Z_out (XE)].

For PHS blocks, q=‖X_ee‖F²−‖X_he‖F². Frobenius Cauchy–Schwarz gives

    |q(X)−q(Y)|
      ≤(‖XE‖F+‖YE‖F) ‖(X−Y)E‖F
      ≤2n ε.                                        (5)

Therefore |g(X)−g(Y)|≤2Nε for square local-reflection readout, and |c(X)−c(Y)|≤2nε for rectangular or square transmission readout. No determinant interpretation is added to the rectangular case.

For square 2N×2N contractions, multilinearity of determinant and the Hadamard column bound give

    |det X−det Y|≤2N ε.                              (6)

Each of the 2N telescoping determinants has one difference column of norm at most ε and all other columns of norm at most one. This proves (6) over complex matrices as well as PHS matrices.

For sign preservation there is a useful dimension-independent sufficient test. If X is a PHS contraction with |det X|≥m>0, all its singular values are at most one, so

    σ_min(X)≥|det X|≥m.

If Y is PHS and ‖Y−X‖<m, every X+t(Y−X), 0≤t≤1, remains invertible: its smallest singular value is at least m−‖Y−X‖>0. Its real determinant is continuous and nonzero, hence det Y has the same sign as det X. Y need not be contractive for this sign-only conclusion; to use the conductance-region theorem it must separately satisfy contraction. At equality ε=m, a singular endpoint is possible, so the strict inequality matters.

These error lemmas can be composed with the established reflection/transmission rules. A calibrated matrix approximation still needs a proved connection to the actual device. The finite-temperature adapter supplies a different route, through an admitted averaged-conductance model and its explicit regularity and warm-to-cold discrepancy; it is not equivalent to assuming a matrix error bound.

## 8. Proposed module interfaces and stopping rules

No code expansion is claimed. A faithful implementation would require independently inspectable inputs/certificates for:

1. Matrix dimensions, channel ordering and exact PHS convention.
2. Contraction or unitarity, with a numerical certificate appropriate to the arithmetic used.
3. Square shape for determinant claims; complete electron/hole selection for subblocks.
4. A common parent/source for simultaneously supplied reflection and transmission blocks.
5. For feedback, the actual port connection and an invertibility/resolvent certificate, or a separately proved generalized singular procedure.
6. The intended readout, current sign, units, energy and temperature model.
7. A justified uncertainty budget and the target being certified.

An absent certificate should yield “not established under this contract,” rather than an arbitrary physical label. A singular inverse request should be rejected by this regular formula, without asserting the underlying physical system does not exist. Evidence inconsistent with contraction or channel normalization should be reported as inconsistent premises.

The direct products, inverse bounds and feedback formula above are finite-matrix mathematics. No choice of a small matrix cutoff proves claims over every geometry, microscopic Hamiltonian, interacting transistor, temperature or measurement family. The reusable value comes from preserving exact contracts and making model-specific obligations visible.

## Sources and verification record

Fresh primary-source reading for this draft: Beenakker's Majorana/scattering relations; Kostrykin–Schrader Sections 3–4, particularly Theorem 3.8 and the generalized inverse discussion; Cervera–van der Schaft–Baños Section 4.2/Proposition 16; Rosdahl Eqs. (3)–(5). The draft derives its elementary closure and error statements explicitly rather than importing a claim of new physics from those sources. This is a bounded directed prior check, not an exhaustive novelty audit.

Existing exact suppliers:

- [All-channel determinant/conductance region and review](https://github.com/Sodelin/Research-Commons/blob/f79a9a7626de25a58ee33d4a3dbff00f9f3f3db1/research/2026-10-16-nanowire-fixed-lead-nonseparation/all-channel/README.md).
- [Reviewed transmission corollary and indicator scope](https://github.com/Sodelin/Research-Commons/blob/11797fe733489a74ef1ad71696ded0fdc1e225bb/research/2026-10-16-nanowire-fixed-lead-nonseparation/indicator-register/README.md).
- [Conditional thermal adapter and independent review](https://github.com/Sodelin/Research-Commons/blob/e8c71a1ddfb5aafae97eb1de06ba4d02be928e92/research/2026-10-16-nanowire-fixed-lead-nonseparation/finite-temperature/README.md).

No numerical experiment, proof-assistant compilation, installation, device operation or public release was performed for this draft. Independent review is requested before accepted status or publication.
