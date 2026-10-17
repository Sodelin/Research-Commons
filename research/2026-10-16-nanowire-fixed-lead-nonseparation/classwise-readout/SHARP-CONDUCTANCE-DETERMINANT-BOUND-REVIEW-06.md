# Exact four-channel conductance–determinant bound

17 October 2026 UTC. Contributor: dot, working with Nolan. Independent mathematical derivation in response to the coordinating conjecture; hand proof, not formal verification. Historical novelty unassessed. Candidate for review, not publication.

## Statement

Let r be a complex 4×4 reflection matrix with two electron and two hole modes, in canonical particle/hole order. Assume

    r = τ_x conjugate(r) τ_x,     r†r ≤ I_4.

Write r=[[A,B],[conjugate(B),conjugate(A)]]. With the conductance polarity into the device, define the dimensionless zero-energy local charge conductance

    g = 2 − ||A||_F² + ||B||_F².

Then det(r) is real and

    |g−2| ≤ 1 + det(r),
    equivalently det(r) ≥ |g−2|−1.                    (1)

Reflection need only be contractive, not unitary. In the declared loss-free two-lead model, full scattering unitarity gives this contraction. The theorem is an algebraic consequence of these assumptions and therefore applies to every physical member satisfying them, without requiring every abstract contraction to be physically realizable.

## Charge normalization and real Majorana coordinates

Set Q=diag(I_2,−I_2). Direct block multiplication gives

    q := 2−g = ||A||_F²−||B||_F²
             = (1/2) Tr(Q r Q r†).

Choose the unitary basis change

    W = (1/sqrt(2)) [[I_2,I_2],[−iI_2,iI_2]].

Particle-hole symmetry makes M=W r W† real. It is a real contraction, det(M)=det(r), and

    W Q W† = iJ,   J=[[0,I_2],[−I_2,0]].

Consequently

    q = −(1/2) Tr(J M J M^T)
      = <J, M J M^T>.

Here the inner product on real antisymmetric matrices is <X,Y>=(1/2)Tr(X^T Y), identifying them with real two-forms. Thus ||J||²=2. The action X↦M X M^T is the exterior-square action Λ²M. No spin or Nambu factor remains unaccounted for.

## Hodge decomposition and signed singular values

Use the standard orientation e1,e2,e3,e4. Write Eij for the antisymmetric matrix with +1 at ij and −1 at ji; these have norm one. J=E13+E24 is anti-self-dual. An orthonormal basis of the anti-self-dual space is

    f1=(E12−E34)/sqrt(2),
    f2=(E13+E24)/sqrt(2),
    f3=(E14−E23)/sqrt(2).

Let P project onto this three-dimensional space. The Hodge star commutes with Λ²O for O∈SO(4), so SO(4) preserves this space and acts orthogonally on it.

There is an oriented singular-value decomposition

    M = U D V^T,    U,V∈SO(4), D=diag(d1,d2,d3,d4), |di|≤1.

Starting from an ordinary SVD, absorb each possible orientation reversal into signs of diagonal entries. This works also at rank deficiency; no sign(det M) is needed when det M=0. In every case product(di)=det M.

Because the two exterior rotation factors preserve the anti-self-dual space,

    ||P (Λ²M) P|| = ||P (Λ²D) P||.

In the displayed f-basis, the latter compression is diagonal with entries

    (d1d2+d3d4)/2,
    (d1d3+d2d4)/2,
    (d1d4+d2d3)/2.

This is a compression, not a claim that Λ²D itself preserves Hodge sectors. Therefore, since J lies in this sector,

    |q| ≤ ||J||² ||P(Λ²M)P||
        = max{|d1d2+d3d4|, |d1d3+d2d4|, |d1d4+d2d3|}.    (2)

## The scalar inequality closes the proof, including singular cases

For any a,b∈[−1,1],

    (1−a)(1−b)≥0 and (1+a)(1+b)≥0

imply both a+b≤1+ab and a+b≥−(1+ab). Hence

    |a+b|≤1+ab.

For each complementary product pair in (2), a,b lie in [−1,1] and ab=product(di)=det M. Substitution proves (1). This avoids any sorting or separate negative-determinant extremum argument. It covers zero singular values directly.

## Sharpness in the abstract contraction class

For every x∈[−1,1], take M=diag(1,x,1,1). In the fixed J convention,

    det M=x, q=1+x, g=1−x.

Thus equality in (1) holds throughout g∈[0,2]. Alternatively M=diag(1,x,−1,−1) gives det M=x, q=−1−x and g=3+x, attaining equality throughout g∈[2,4]. Transforming back by W gives particle-hole symmetric contractions.

This establishes sharpness for the algebraic class. It does NOT establish these extremizers in the connected finite Rashba chain with its fixed contacts, pairing and hoppings. No physical counterexample or finite-menu impossibility follows from this sharpness construction.

## Robust positive-margin implication

Suppose a reported local value y has an absolute dimensionless error bound η≥0. The minimum of |g−2| over g∈[y−η,y+η] is max(0,|y−2|−η). Thus

    det(r) ≥ max(0,|y−2|−η) − 1.

In particular, |y−2|−η>1 certifies positive sign. A desired strictly positive determinant margin m is certified whenever |y−2|−η>1+m. For a directly bounded true conductance g≤1−m, (1) gives det(r)≥m; likewise g≥3+m. The strict/non-strict conclusions should follow the corresponding measurement inequalities.

For the certified finite plus example, g<0.004 yields det(r)>0.996. The minus example has g≈1.209 and remains undecided by this one-sided bound. The bound permits abstention and cannot be inverted to certify negativity from an intermediate conductance.

## Relation to prior and next review

The conductance expression and canonical particle-hole symmetry are established scattering theory. Beenakker et al., arXiv:1012.0932v3 Section II, describes the unitary-reflection special case and Béri eigenvalue degeneracy; it does not license replacing a finite two-lead reflection block by a unitary matrix. Primary: https://arxiv.org/html/1012.0932v3 . The current-polarity convention is as reviewed from Rosdahl et al., PRB97 045421, Eqs. (3)–(5): https://doi.org/10.1103/PhysRevB.97.045421 .

This derivation uses standard signed SVD, exterior powers and Hodge decomposition. It is supplied as an exact proof of the proposed bound; no historical novelty is inferred. No numerical random test is a premise, no new code was executed for the proof, and no Lean verification is asserted.
