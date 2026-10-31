# AppendixB: an independent3599 bound using only real finiteness

This optional derivation is weaker numerically than the main499 bound, but does NOT need the stronger exclusion of complex components through strict points. It separates that logical issue explicitly.

**Lemma.** Let nonzero U,V∈R[x,y] have total degrees at most M,N, where M≥N≥1. If their common real zero set in an OPEN set W is finite, it has at most MN points.

Take the full real gcd G, degree d≤N, and write U=GA,V=GB with A,B coprime. They are coprime overC too, since a common complex factor and its conjugate would give a real common factor. OffG, Bézout bounds the intersections by(M−d)(N−d). Nonzero constant residual factors give no intersections.

Let G_sf be the squarefree part, of degree e≤d. Every real zero of G in W is isolated, or it would yield infinitely many common zeros of U,V in W. Such a point has ∇G_sf=0 by the real implicit-function theorem. Choose a real constant direction v for which D_vG_sf is coprime to G_sf overC. This is possible: for each of finitely many complex irreducible factors h of the squarefree G_sf, divisibility of D_vG_sf by h imposes a proper linear restriction on v. Both coordinate derivatives cannot be divisible by h in characteristic0, by degree reduction. A finite union of proper real direction subspaces cannot coverR².

Bézout then bounds these singular points by e(e−1)≤d(d−1); a linear squarefree polynomial has no singular points. Combining both parts gives

 (M−d)(N−d)+d(d−1)=MN−d(M+N+1)+2d²≤MN.

The quadratic is convex for0≤d≤N, and its endpoint values are MN and N(N−1)≤MN. Constants are handled trivially. This proves the lemma even with common complex components or isolated real points on them.

For the main note's P,Q, total degree P≤61 and Q0≤60. Exact division by1−p gives total degree Q≤59. Both polynomials are nonzero by the pole arguments. The reviewed no-AP result makes their strict real common zero set finite. Apply the lemma with W=(0,1)²,M=61,N=59 to obtain3599 types. The stronger main theorem separately uses complex-component exclusion and gives499.

Classical source: J.S. Milne, [*Elliptic Curves*, second edition, Theorem1.18](https://www.jmilne.org/math/Books/EC2.pdf), gives the projective Bézout degree-product count; the affine inequality follows by homogenization. No use of Bézout assumes coprimeness before the explicitly stated gcd removal.
