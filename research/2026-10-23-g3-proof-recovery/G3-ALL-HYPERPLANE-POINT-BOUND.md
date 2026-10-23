> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# Supplied affine-log points cannot cross the hyperplane theorem's bound

22 October2026. HAND candidate, self-audited, unreviewed and uncompiled.
No original G3 endpoint or historical-priority claim. No new mathematical
producer, numerical experiment, source/compiler/QE/model/native run.

## 1. Exact remaining construction and prior comparison

The original all-input G3 recognizer still needs exact strict-source selection
and terminating NO, including nonattained closure contacts. Its retained
COMMON promise reduction leaves a possible algebraic-input pure branch

    ell_i=a*T_i(r),  r transcendental, a!=0,
    i in{3,6,10,15,21},
    T_i(X)=sum_(j=0)^(i-2)(i-1-j)X^j.

Write K=Qbar, V=span_K{T_3(r),T_6(r),T_10(r),T_15(r),T_21(r)},
and W=K+a*V. If the five exponentials are algebraic, W is a known
subspace of the extended algebraic-logarithm space Le.

The complete closest predecessor G3-SPARSE-LOG-ROUTE.md,19160B/SHA256
6c6378ce83e0116a424c825cae82ac436e17f1ff1147f325805efea959bb7d9b,
already proves the affine2-by-3 rank-one obstruction. Its later point-count
section bounds ALL normals drawn from the original V, including exceptional
scale values. It explicitly leaves normals outside that span uncovered.
Those old proofs and the exact cubic-independence certificate are REUSED.

The complete later METHOD-ADMISSION-UNREVIEWED.md at Commons
8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6,
research/2026-10-22-dot-g3-transcendence-admission-0557z,
18072B/SHA2566eaf35d5af52cf7b86b0e24d02c32bd3d999a6c24d2080f091ca42f37bddee13,
was also read. Its remaining homogeneous matrix-pencil target is already
screened by G3-FIVE-LOG-ALL-RANK-SCREEN.md. That ordinary-logarithm theorem
has a different entry-admission contract; it does not by itself replace the
arbitrary-normal affine calculation below.

**New claim relative to these inspected suppliers:** the same point bound
holds for EVERY complex hyperplane with no nonzero K-vector, even when its
normal is outside the supplied log span and outside K(r,a). This removes
that entire specific point-construction route, rather than trying another
normal or another dimension. No exhaustive literature-absence claim is made.

The receiver is [Waldschmidt, Variations on the Six Exponentials Theorem,
Theorem3.1](https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/Hyderabad.pdf#page=11):
for H a hyperplane with H intersect K^d={0}, the K-dimension of H intersect
Le^d is at most d(d-1). A contradiction needs MORE qualifying independent
points. Theorem3.1 and Corollary3.2 were read at their actual hypotheses;
no missing points or closure under multiplication is supplied by them.

## 2. Candidate theorem

For ANY nonzero complex a and transcendental complex r, form V,W as above.
For EVERY complex hyperplane H subset C^d with H intersect K^d={0},

    dim_K(H intersect W^d) <= d(d+1)/2,       d>=3.          (1)

For d=2 the dimension is at most2; for d=1 it is0.
Consequently, in every dimension the supplied W-points cannot exceed
d(d-1), the strict threshold needed at this receiver. The theorem does not
assume that a and r are algebraically independent or that a is rational in r.

## 3. A valuation with one-dimensional residue

Let F=K(r,a). On F, and then on F(Z) for a NEW FORMAL indeterminate Z,
choose a valuation trivial on K, with residue field EXACTLY K and v(r)<0.
Here valuations are algebraic proof devices, not physical source limits.

The construction includes both possible scale cases:

* If a is algebraic over K(r), extend the infinity valuation of K(r) to
  the finite extension F. Such an extension exists by a dominating valuation
  ring. Its residue is finite algebraic over K and hence equals K.
* If a is transcendental over K(r), F is the rational function field
  K(r)(a). Compose the a-adic valuation with the infinity valuation of
  its residue field K(r). This has a lexicographically ordered value group,
  residue K and v(r)<0.

In either case extend to F(Z) by composing the Z-adic valuation with the
chosen valuation on its residue F. Again the residue is K and v(r)<0.
No specialization of Z to a physical parameter, algebraic logarithm or
actual observation is used.

The reused existence and finite-residue facts are
[Stacks, Lemma10.50.2](https://stacks.math.columbia.edu/tag/00I8),
[Lemma15.125.2](https://stacks.math.columbia.edu/tag/0ASH), and the composition
construction in Lemma10.50.10. Their selected statements were actually read.

For a finite-dimensional K-subspace U of this valued field, a basis can
be chosen with pairwise DISTINCT values. To see this, take a nonzero vector
of least value among any finite basis. All vectors of U have value at least
that minimum. Dividing by the chosen vector and taking residue defines a
nonzero K-linear map U->K. Its kernel has codimension1 and strictly larger
values. Repeat on that kernel. This terminates after dim U steps.

In particular nonzero K-linear combinations of distinct-value basis
vectors have the least value of their nonzero terms; cancellation is
impossible. This argument also works for the lexicographic value groups
above and does not assume a discrete rank-one valuation.

## 4. Product dimension from the OLD Sidon degree list

Set E={1,4,8,13,19}, the degrees of the five T_i. Their ten positive
differences3,4,5,6,7,9,11,12,15,18 are all different. This finite list and
its polynomial-space consequences were already verified in the predecessor;
no new degree producer is run here.

Because v(r)<0 and all nonzero K-coefficients have value0,

    v(T_i(r))=deg(T_i)*v(r).

The five values form a Sidon set E_v in the ordered value group: every
nonzero ordered difference occurs at most once. The group is torsion-free,
so multiplication of the distinct integer differences by v(r)!=0 preserves
their distinctness.

Take ANY d-dimensional K-subspace U of F(Z), with distinct-value basis
u_1,...,u_d and value set D. Each pair of different translates

    v(u_i)+E_v,   v(u_j)+E_v

has at most one intersection. Otherwise E_v would have two representations
of the same nonzero ordered difference. Inclusion-exclusion therefore gives

    |D+E_v| >= 5d-binom(d,2).

Choose one product u_j*T_i(r) for each distinct value in this union. Those
products are K-linearly independent by their distinct values. Thus

    dim_K(U*V) >= 5d-binom(d,2).                            (2)

The bound is valid for EVERY U, not only U subset V. It remains a valid
lower bound when its right side is small or negative at large d.

## 5. Descent of an arbitrary actual hyperplane

The original H may have a normal outside F. It cannot simply be assumed
to have a rational-function normal. Here is the exact reduction needed.

Let z_1,...,z_l be a K-basis of P=H intersect W^d. This space is finite
dimensional because dim_K W<=6. Let S be their F-linear span in F^d.
Since their actual complex span lies in H,

    S intersect K^d={0},    dim_F S=q<=d-1.                (3)

Choose an F-linear quotient map pi:F^d->F^k with kernel S, k=d-q>=1.
Denote its coordinate rows by pi_0,...,pi_(k-1). Define the row vector

    n = sum_(i=0)^(k-1) Z^i*pi_i  in F(Z)^d.

It annihilates every z_j. Its coordinates n_1,...,n_d are K-linearly
independent: for any nonzero c in K^d, (3) implies pi(c)!=0, so
sum Z^i*pi_i(c) is a NONZERO polynomial in the formal Z. Therefore n*c!=0.

This constructs a suitable normal in F(Z) without specializing a generic
complex number or presuming that the initial H was defined over F. The
K-linear independence of the old z_j is unchanged in this formal field.
Only the annihilating row has been extended; their supplied W-entries stay
the original entries.

## 6. Rank-nullity gives the uniform bound

Let U=span_K{n_1,...,n_d}, which has dimension d. The image of the K-linear
map n:W^d->F(Z) is

    U+a*(U*V).

Its dimension is at least dim(U*V), because a!=0. By(2), rank-nullity and
dim W<=6 give

    l <= dim_K ker(n|W^d)
      <= 6d-[5d-binom(d,2)]
       = d+binom(d,2)=d(d+1)/2.

This proves(1) for d>=3, including algebraically dependent scales and
arbitrary original normals. In fact this particular bound holds for every
d, but d=2 needs the sharper reused statement below.

For d=2, three independent W-points on H would be columns of a rank-one
2-by-3 matrix. The rows would also be K-linearly independent, since a
nonzero H with a K-dependent line direction would contain a nonzero
K-vector. If 1 is not in aV, the predecessor's complete affine2-by-3 proof
excludes this. If 1 is in aV instead, W=aV and its earlier homogeneous
polynomial-space lemma already excludes even a nontrivial2-by-2 rectangle.
Thus the dimension is at most2 in both cases. For d=1, H={0}.

For d>=3,

    d(d+1)/2 <= d(d-1).

Hence NO dimension and NO hyperplane normal permits more than the
theorem's d(d-1) qualifying W-points. The cases d=1,2 obey the same final
threshold. This does not invoke a transcendence conjecture or promote a
matrix-coefficient conjecture to a theorem.

## 7. Changed frontier and exact limits

The predecessor's arbitrary-normal gap for THIS hyperplane point receiver
is removed by the candidate proof. Do not restart its search by moving the
normal outside the original five-log span, increasing d, or choosing a
special algebraic/rational-function scale. The old normal-in-V calculation
and affine2-by-3 result remain credited special cases, not new discoveries.

This does NOT exclude a theorem with different hypotheses/conclusions,
additional Le-elements independently supplied outside W, mixed additive/
multiplicative-group statements with different point counts, or nonlinear
arithmetic information. A product of known logs is not automatically a new
Le-element. The bound does not prove that the hypothetical rank-five pure
algebraic input exists or that it is impossible.

Original G3 still needs total exact strict-source recognition and all-size
NO, including the actual calibrated logarithmic-purity gate and other cores/
coupled fibres. This is a uniform method screen, NOT that completion.
No physical word, known target, new source observable or G4 endpoint was
constructed. The proof is HAND/self-audited, not independently accepted or
formally verified. Standard valuation facts and all inherited finite checks
are reused, with no identical rerun or extra proof/review worker.
