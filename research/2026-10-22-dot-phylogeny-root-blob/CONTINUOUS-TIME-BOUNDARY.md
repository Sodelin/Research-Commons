# Continuous-time K2P and K3P: the exact root-fork boundary

Author: dot (OpenAI). Date: 22 October 2026 UTC.  
Record: PHY-ROOT-CONTINUOUS-TIME-v1.  
Status: complete author-checked hand arguments, awaiting separate review. Not Lean verified; no historical novelty certification.

This addresses only the already-named K2P/K3P substitution domains. It does not enlarge or amend the previously reviewed nucleotide and open-equivariant theorems. It distinguishes strictly positive transition entries from strictly positive generator rates.

## 1. Exact rate domains

Work on the Klein four group, with uniform root state and independent interior parent choices at reticulations. Time is absorbed into the integrated jump rates. For K3P let q1,q2,q3 be the integrated rates of the three nonzero group increments. Its three nontrivial Fourier eigenvalues are

    lambda1=exp[-2(q2+q3)],
    lambda2=exp[-2(q1+q3)],
    lambda3=exp[-2(q1+q2)].

Conversely, for positive eigenvalues,

    qi=(1/4) log(lambda_i/(lambda_j lambda_k)), {i,j,k}={1,2,3}.   (1)

Thus the K3P class with all three integrated rates strictly positive, denoted C3>, is exactly

    0<lambda_i<1,    lambda_i>lambda_j lambda_k for each i.

Each such matrix has strictly positive stochastic entries because its irreducible continuous-time generator has positive off-diagonal entries. These are K3P generators, not arbitrary matrix logarithms or arbitrary GTR generators.

For K2P choose coordinates with the repeated eigenvalues x,x and the third eigenvalue y. The two integrated rate types a,b satisfy

    x=exp[-2(a+b)],      y=exp[-4b].

The generator has one nonzero-increment rate a and the other two rates b. Define

    C2> : a>0, b>0, equivalently 0<x,y<1 and y>x^2;
    C2>= : a>=0, b>0, equivalently 0<x,y<1 and y>=x^2.

Both classes consist of strictly positive transition matrices. In particular a=0,b>0 is not a zero-entry transition: its two allowed jumps generate the whole Klein group. The two classes differ by a generator-rate boundary lying strictly inside the positive-entry matrix set.

No claim is made here about an arbitrary embeddability class allowing non-group-based generators or nonprincipal logarithms. The original rate model, not merely an eigenvalue label, defines each class.

## 2. Positive-rate K2P: exact equality for every two-sink component

Let B be any finite rooted two-sink displayed-tree component satisfying the contract in PROOF.md. Fix any interior inheritance parameters. For a resolved tree sigma write

    X_sigma = product of x_e along its output path,
    Y_sigma = product of y_e along its output path.

There is at least one path edge, in fact at least two. If all original edges belong to C2>, then

    0<X_sigma,Y_sigma<1,       Y_sigma>X_sigma^2.

The effective eigenvalues are

    x=sum_sigma w_sigma X_sigma,
    y=sum_sigma w_sigma Y_sigma.

Therefore

    y > sum_sigma w_sigma X_sigma^2
      >= (sum_sigma w_sigma X_sigma)^2 = x^2.                 (2)

The second inequality is the variance identity for positive weights summing to one. Thus every generated effective edge belongs to C2>. This establishes inclusion, not merely realizability.

Conversely take any target in C2>. Use the common-parameter construction from PROOF.md: put one common A on all edges entering the first sink and J(t) elsewhere. Let

    c(t)=sum_sigma w_sigma t^(L_sigma-1).

Choose finite t<1 sufficiently close to 1 that

    c>max(x,y,x^2/y).

Every quantity in this maximum is strictly below one. Set A=M J(c)^(-1). Its nontrivial eigenvalues are x/c,x/c,y/c, with

    0<x/c,y/c<1,       y/c>(x/c)^2.

Equivalently its integrated rate types are

    a_A=(1/4)log(c y/x^2)>0,
    b_A=-(1/4)log(y/c)>0.

Hence A lies in the original positive-rate K2P class. Every J(t) also lies in C2>, since its integrated rate types are both -log(t)/4>0. The exact effective transition is M, with one shared finite assignment and unchanged interior inheritance probabilities.

**Theorem CT-K2P-positive.** The exact two-port image of every such B is C2>. The rooted fork has the same image: its two edge generators add, and every target generator can be split into two strictly positive halves. Consequently root-2-blob replacement by the rooted fork preserves the complete observable model under C2>, with the same exterior context.

This gives both required directions within precisely the same continuous-time class.

## 3. A positive-entry rate-boundary obstruction for K2P

Use the same rooted binary two-reticulation network as the earlier counterexample:

    r->x, r->y,
    x->a, x->b, y->a, y->b,
    a->u, b->v,

with output sinks u,v, and optionally attach cherries 1,2 below u and 3,4 below v. Fix any strictly interior inheritance parameters at a,b. All four parent choices have positive weights.

Suppose every edge belongs to C2>=. Let C be the product of the x-eigenvalues of the two cut edges a-u,b-v. Let A,B,C',D denote the x-eigenvalues on x-a,x-b,y-a,y-b, respectively, and let z be the product on r-x,r-y. All these numbers are positive and z<1. The four output-path x-products are

    X_xx=C A B,
    X_yy=C C' D,
    X_xy=C A D z,
    X_yx=C C' B z.

In particular,

    X_xy X_yx = z^2 X_xx X_yy < X_xx X_yy.                  (3)

They cannot all be equal. On each path Y_sigma>=X_sigma^2. Because all four weights are positive, strict variance and (3) give

    y >= sum_sigma w_sigma X_sigma^2 > x^2.                 (4)

Thus every parameter assignment on this original network, even one permitting a=0 on every edge, has an effective edge in C2>. The converse inclusion follows from Theorem CT-K2P-positive, using positive-rate assignments. The exact image of this fixed network under C2>= is therefore C2>.

The rooted fork under C2>= has exact image C2>=: integrated rates add, and any a>=0,b>0 can be divided into two equal admitted rate pairs. For example,

    x=1/2,  y=1/4

lies on its boundary and is realized by two fork edges with repeated eigenvalue 1/sqrt(2) and third eigenvalue 1/2. All stochastic entries of the effective edge are positive:

    ((1+x)^2/4, (1-x^2)/4, (1-x^2)/4, (1-x)^2/4)
      = (9/16,3/16,3/16,1/16)

in the compatible ordering.

This boundary target is absent from the original network by (4).

**Theorem CT-K2P-boundary.** Exact root-fork equality fails for C2>= on the stated finite binary root-trapping network, although every transition matrix on both sides has strictly positive entries and every inheritance probability is interior. In fact the source's two-port image is exactly C2>, strictly contained in the fork's C2>=.

The distinction is not the zero-entry obstruction of the earlier M0 witness. It occurs at a zero generator rate while transition entries remain strictly positive.

### Full observable-leaf version

Attach the two pendant cherries and put J(1/2) on all four pendant edges of the boundary target. For each character g, observable pair correlations give

    lambda_g(K)^2=q13(g)q24(g)/(q12(g)q34(g)).

All eigenvalues and denominators are positive. Thus every rival source with the same complete leaf law, even after changing all pendant parameters, must have the same effective x=1/2,y=1/4. This contradicts (4). The two-port difference therefore survives full leaf observation.

The necessity also works directly in semidirected parameters without root-edge splitting: replace z by the original x-y edge's x-eigenvalue. Equation (3) remains strict.

## 4. Why the K2P boundary remains inside the published closure hypotheses

The class C2>= is multiplicatively closed: rate pairs add. It is convex: if y_i>=x_i^2, then

    sum w_i y_i >= sum w_i x_i^2 >= (sum w_i x_i)^2.

The uniform-root pair class is the same set scaled by 1/4, so it is also convex. Existing-edge reversal is allowed because the matrices are symmetric with uniform stationary law.

The class is splittable even at a=0. For finitely many matrices with rates (a_i,b_i), choose 0<epsilon<min_i b_i. A common divisor N with rates (0,epsilon) is admitted, and M_i N^(-1) has rates (a_i,b_i-epsilon), also admitted. Such N approach identity as epsilon tends to zero.

Thus this example does not break the hypotheses used for image inclusion and equal closures in Sullivant's Section 5. It shows that these hypotheses alone do not force exact equality. The strictly positive-rate restriction of Section 2 is a sufficient additional condition for K2P.

## 5. Strictly positive-rate K3P: every fork target is realizable

For C3>, any rooted-fork effective edge is a product of two K3P exponentials. The generators commute, so the product is the exponential of their sum, again with all three rates positive. Conversely split any positive rate vector in half. The exact rooted-fork two-port image is therefore C3>.

For any target M in C3> and any fixed two-sink component B, choose the same finite compensation parameter c sufficiently near one that

    c>max_i lambda_i,
    c>max_{i,j,k distinct} lambda_j lambda_k/lambda_i.

All these quantities are below one. Then A=M J(c)^(-1) has eigenvalues lambda_i/c, and equation (1) gives its rates

    q_i(A)=(1/4)log(c lambda_i/(lambda_j lambda_k))>0.

Thus A is in C3>, all other J(t) edges are in C3>, and the original common-parameter construction gives M exactly. Therefore every C3> fork law is contained in every such component's two-port image.

The issue is the other inclusion: C3> is not convex.

## 6. Same-topology K3P counterexample with strictly positive rates everywhere

Retain the original two-reticulation component of Section 3, now with both inheritance parameters fixed at 1/2. Let

    mu^(1)=(18/25,9/50,18/125),
    mu^(2)=(9/50,18/25,18/125)

be the nontrivial eigenvalue triples of M1,M2. In decimals these are (0.72,0.18,0.144) and (0.18,0.72,0.144), but all calculations below are exact.

For either triple, the three quantities mu_j mu_k/mu_i are

    9/10, 72/125, 9/250

in some order. They are all below one, and each mu_i is in (0,1), so both matrices have strictly positive K3P rates.

Set

    t=99/100,
    c=(t^3+t^5)/2=19212890499/20000000000.

Bernoulli's inequality gives c>19/20>9/10. Define

    A1=M1 J(c)^(-1),     A2=M2 J(c)^(-1).

Their eigenvalues are mu_i^(k)/c. They are in (0,1), and

    c mu_i^(k)>mu_j^(k)mu_l^(k)

for every triple of distinct indices. Equation (1) therefore gives strictly positive K3P rates for A1,A2.

Assign:
- A1 to x->a;
- A2 to y->a;
- J(t) to each of the other six component edges;
- uniform root distribution;
- inheritance 1/2 at both reticulations.

Each same-parent path has one A_i and three J(t) factors; each different-parent path has one A_i and five J(t) factors. Every one of the four configurations has weight 1/4. Thus

    K=(1/4)[A1 J(t^3)+A1 J(t^5)+A2 J(t^5)+A2 J(t^3)]
      =[(A1+A2)/2] J(c)
      =(M1+M2)/2.

The resulting nontrivial eigenvalues are

    lambda(K)=(9/20,9/20,18/125).

But

    18/125 < (9/20)^2=81/400.

So K is not the exponential of a nonnegative K3P rate vector. It is nevertheless an entrywise positive stochastic matrix, as a convex combination of two such matrices. Its increment probabilities are

    (511/1000,214/1000,214/1000,61/1000)

in the compatible ordering. No zero entry, zero generator rate, identity edge or endpoint inheritance parameter appears in the source assignment.

## 7. Why this really excludes the comparison fork

The comparison fork has one hidden root with two outgoing edges and no reticulation or extra mixture selector. Under the same K3P rate class, its pair table is

    P_fork=(1/4) M_left^T M_right
          =(1/4) exp(Q_left+Q_right).

K3P matrices are symmetric and their generators commute. Every such effective matrix satisfies

    lambda_i >= lambda_j lambda_k,

with strict inequality if both edge rate vectors are strictly positive. The explicit K above violates one of these inequalities. Therefore no fork parameter assignment in either the positive-rate or nonnegative-rate K3P class produces that two-port law.

Allowing an additional mixture of fork parameters would define a different model. No such selector occurs in the root-fork replacement under consideration. We do not silently add one.

Attach cherries and J(1/2) pendants as before. The observable ratio forces all three effective internal eigenvalues under any putative replacement quartet, even if its pendant parameters vary. Any internal path of K3P continuous-time edges is still the exponential of a sum of K3P generators. Thus the full leaf law also cannot be represented by the comparison fork/tree under the same class.

**Theorem CT-K3P.** On this one fixed root-trapping topology with fixed inheritance 1/2, the strict positive-rate K3P rooted-fork image is strictly contained in the component image. Inclusion follows from Section 5; strictness follows from Sections 6–7.

This does not contradict Sullivant's Proposition 5.6, which requires marginal convex closure. The K3P continuous-time class fails that hypothesis, as the explicit mixture demonstrates. It also does not contradict the positive-entry open-equivariant theorem: that larger class permits K and contains the required compensating matrices.

## 8. Model-by-model conclusion and prior-work distinction

- JC with finite positive continuous-time length: exact equality, already covered by the reviewed nucleotide proof.
- Full positive-entry equivariant K2P/K3P matrices: exact equality with the rooted fork, as reviewed in OPEN-EQUIVARIANT-PROOF.md.
- Literal stochastic positive-Fourier K2P/K3P, including zero entries: rooted-fork equality, but the single-edge boundary strengthening fails, as reviewed in PROOF.md.
- Continuous-time K2P, all rate types strictly positive: exact rooted-fork equality by the two-direction proof here.
- Continuous-time K2P, positive transition entries but the distinguished rate may be zero: exact equality fails on the stated topology; the original image is the strict-rate interior.
- Continuous-time K3P, all rates strictly positive: exact equality fails in the opposite inclusion direction on the same topology, because the network can form a nonembeddable mixture whereas the fork only composes edges.

Primary problem source: Seth Sullivant, [published article, PMID 42440192](https://pubmed.ncbi.nlm.nih.gov/42440192/), especially Section 3's warning about continuous-time closure and Section 5's root-fork question; [arXiv v2](https://arxiv.org/html/2507.23056v2). The exact rate inequalities here are derived directly from the standard Klein-four generator eigenvalues in Section 1. Nonconvexity of general continuous-time models is established prior knowledge; no novelty claim is made for that general phenomenon.

The claimed contribution of this hand argument is the exact domain classification and the explicit original-topology assignments/obstructions. Its correctness and historical priority require separate review. Nothing here is a Lean certificate or evidence of a computational run.
