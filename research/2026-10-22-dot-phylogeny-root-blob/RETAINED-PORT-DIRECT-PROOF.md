# Direct maximal-root-blob replacement with the original cut matrices fixed

Author: dot (OpenAI), 23 October 2026.
Record: PHY-MAXIMAL-DIRECT-PORT-v1.
Status: complete author-checked hand proof with scoped coordinating-assistant
hand-review PASS on 23 October 2026. See the separate
[review receipt](RETAINED-PORT-DIRECT-REVIEW.md). No Lean elaboration, runtime,
independent-human review or historical novelty certification is claimed.

## 1. Exact improvement, source relation and target

This note adds a direct adapter for a genuine maximal binary root 2-blob.
Its two boundary attachment vertices need not both be internal sinks. It
replaces the blob interior by a fresh rooted fork on those SAME attachment
vertices, keeping BOTH original cut-edge matrices, and every other exterior
parameter, exactly fixed. The earlier subdivision adapter remains valid; it
does not prove this stronger fixed-cut statement because it may change the
cut matrices.

The target is the retained-port rooted fork, not an unrestricted single
semidirected edge. Its two retained ports have indegree one and outdegree
one in the full network. This intermediate graph is a permitted rooted DAG,
not silently a binary phylogenetic network without degree-two vertices.
This note does not assert that arbitrary zero-entry edge parameters may be
split when these degree-two ports or the root are suppressed.

Primary setting: [Sullivant, Section 5, Propositions 5.6–5.7](https://arxiv.org/html/2507.23056v2#S5)
defines a retained-port replacement and asks for exact image equality after
establishing inclusion and a limiting converse. His proposition explicitly
uses two sinks. The present graph argument also covers the nonterminal-port
maximal binary case, using the source binary conventions of
[Brits et al., Definition 2.1](https://arxiv.org/html/2607.12919v3#S2.SS1).
It is not a solution of the broader literal nonmaximal 2-sub-blob contract
in [Brits et al., Section 5.1](https://arxiv.org/html/2607.12919v3#S5.SS1).
The separately recorded definition/operation and rooting-lift blocker is
unchanged.

The algebra reuses [PROOF.md, Sections 3–4](https://github.com/Sodelin/Research-Commons/blob/f8da22c7305d18bf4e9cc3b56d3c82d1aa1da2ad/research/2026-10-22-dot-phylogeny-root-blob/PROOF.md),
[OPEN-EQUIVARIANT-PROOF.md](https://github.com/Sodelin/Research-Commons/blob/808c5f2931878a70dc08faed26e764c43b4a4e37/research/2026-10-22-dot-phylogeny-root-blob/OPEN-EQUIVARIANT-PROOF.md),
and [CONTINUOUS-TIME-BOUNDARY.md, Section 2](https://github.com/Sodelin/Research-Commons/blob/befa68f0095139f5ff747b3b671d8a82e96ac4fc/research/2026-10-22-dot-phylogeny-root-blob/CONTINUOUS-TIME-BOUNDARY.md).
The new obligation is their direct composition with a possibly nonterminal
original boundary port, rather than an assertion that the old two-sink
hypothesis held automatically. The two-sink proof-source package and later
maximal subdivision source package remain entirely unelaborated and do not
formally verify this new argument.

## 2. Graph contract and the terminal-port lemma

Let G be a finite simple binary rooted directed acyclic network. Its unique
root has indegree zero and outdegree two. Every other nonleaf vertex has
degrees (indegree,outdegree)=(1,2) or (2,1), and leaves have indegree one and
outdegree zero. Only labelled leaves are observed. If the original source
class requires the root to be the last stable ancestor of the leaves, keep
that hypothesis; the argument below does not remove it.

Let B be a nontrivial maximal connected bridgeless vertex-induced region
containing the actual root. Assume exactly two edge occurrences cross from
B to its complement in the underlying graph. All references to maximality
and bridges are undirected; all ancestry and path references are directed.

The reviewed graph argument supplies the following facts, repeated here
to expose the exact dependency.

1. Every vertex of G is root-reachable: following incoming edges backwards
   in a finite DAG terminates at the unique source.
2. Each boundary edge of B is a global bridge. Otherwise an undirected cycle
   containing that edge has connected bridgeless union with B, enlarging B
   and contradicting maximality.
3. Each boundary bridge is directed out of B, since a root path must cross
   it to reach its outside endpoint. In particular B is ancestral.
4. Every vertex of the nontrivial connected bridgeless B has internal
   undirected degree at least two. Thus B has no global leaf; its root has
   no boundary edge; each nonroot vertex, of total degree three, has at most
   one boundary edge. The two edges have distinct nonroot sources a and b.
5. Every internal sink of B is one of these two sources: a different sink
   would be a global leaf inside B. Finite acyclicity gives at least one
   internal sink. Label such a sink b and the other boundary source a.

Since b has no internal child and exactly one boundary edge, it has total
outdegree one. Therefore it is a reticulation with indegree two. Both its
parents are in B by ancestry, and they are distinct because G has no
parallel edges. At least one of these parents is not a. Vertex a is not a
descendant of b inside B; no assertion that a is itself a sink is needed.

For reference, the prior scoped graph receipt is
[ROOT-BLOB-GRAPH-REVIEW.md](https://github.com/Sodelin/Research-Commons/blob/7671217d457440a0fae8b435015f772ea0302845/research/2026-10-22-dot-phylogeny-root-blob/ROOT-BLOB-GRAPH-REVIEW.md).
Its earlier fixed-cut exclusion remains an accurate description of that
earlier proof. This note is a separate proposed strengthening.

## 3. Resolutions, path lengths and one common assignment

Fix once and for all a strictly positive normalized parent-choice vector
at each nonroot vertex of B. The choices at different vertices are
independent. Indegree-one vertices have their unique choice with weight
one. These original vectors are not adjusted during any realization below.

For a complete selector sigma, retain its chosen incoming edge at every
nonroot vertex. Following selected parents terminates at the root, so the
retained graph is a rooted tree on the original vertices of B. Write w_sigma
for the product of its prescribed choice weights. Every w_sigma is positive
and their finite sum is one.

Let L_sigma be the number of edges on its undirected a-to-b path. Since a
and b are distinct, L_sigma>=1. Since b is a sink, that path contains
exactly one selected edge entering b and no other edge entering b.

Choose at b a parent different from a, and make any choices elsewhere.
In that resolution a and b are not adjacent: its sole edge incident to b
connects b to that other parent. Consequently at least one selector sigma_0
has L_sigma_0>=2 and w_sigma_0>0. Other selectors may have L_sigma=1; they
must not be discarded or assumed absent.

Put the SAME matrix A on every original edge entering b, and the SAME reset
matrix E(t) on every other internal edge, with 0<t<1. This is one assignment
on the original edge occurrences. No matrix depends on the selector.
For each path the number of reset edges is L_sigma-1, possibly zero. Define

    c(t) = sum_sigma w_sigma t^(L_sigma-1).

Then 0<c(t)<1: every summand lies in (0,1], and the sigma_0 summand is
strictly below one. Finiteness gives c(t)->1 as t increases to 1. Thus every
strict threshold c(t)>eta with eta<1 can be met at a finite t<1. If desired,
Lmax=max_sigma L_sigma and Bernoulli's inequality give
c(1-1/n)>=1-(Lmax-1)/n for integers n>1.

## 4. Literal Fourier JC/K2P/K3P domain, including zero edge entries

Let K be the Klein four group. A stochastic group-based matrix has the form
M_p(x,y)=p(y-x), for a probability distribution p on K. Let T_3 consist of
those matrices for which all three nontrivial Fourier eigenvalues lie in
(0,1). T_2 imposes the designated equality of two eigenvalues, and T_J
requires all three equal. Entries are NONNEGATIVE, not assumed positive.
Let T_*^+ denote the strictly positive-entry subfamily. The root is uniform.

### 4.1 Forward image: why even K3P becomes strictly positive

For every admitted p, inversion at zero gives

    p(0)=(1+lambda_1+lambda_2+lambda_3)/4>0.

If its support had at most two elements, it would be contained in {0,h}
for a nonzero h, or consist only of 0. A nontrivial character equal to 1 on
h is then equal to 1 on all of the support. Its eigenvalue would be 1,
contrary to admission. Hence the support has at least three elements.
This argument applies separately to the entire T_3 class, not merely T_2.

For two such probability distributions p,q and any g, the subsets
supp(p) and g-supp(q) of the four-element group intersect. At an element
h in their intersection, p(h)q(g-h)>0. Hence every entry of their convolution
is positive. Additional probability factors preserve positivity.

In each resolved tree, ordinary marginalization of unused branches and
uniform-root reversibility give the ordered pair table

    P_sigma(X_a=i,X_b=j) = (1/4) (K_sigma)_{ij},
    K_sigma = product of M_e over the a-to-b path.

All matrices are symmetric and commute, so path orientation makes no
difference. Every path product has nontrivial eigenvalues in (0,1), is
stochastic, and preserves the designated JC/K2P equalities. Products with
L_sigma>=2 are strictly positive by the support argument. Since sigma_0
has positive weight, their mixture

    K_B = sum_sigma w_sigma K_sigma

is strictly positive in every entry, including when some one-edge terms
have zeros. Its Fourier eigenvalues are convex combinations of numbers in
(0,1), and the same equality constraints persist. Therefore K_B is in T_*^+.

### 4.2 Reverse image: exact finite realization

Take any target M in T_*^+. Let U have all entries 1/4 and put
J(t)=tI+(1-t)U. Use Section 3's common assignment with E(t)=J(t).
For every selector,

    K_sigma = A J(t^(L_sigma-1)).

This identity includes a one-edge path, for which the reset factor is
algebraically J(1)=I; no actual original edge is assigned an identity.
The affine dependence of J on its scalar gives

    K_B = A J(c(t)).

Let m=min_ij M_ij>0 and lambda_max=max_i lambda_i(M)<1. Choose a finite
t<1 with c=c(t)>max{0,lambda_max,1-4m}, and set

    A=U+(M-U)/c.

Its entries [M_ij-(1-c)/4]/c are positive, its rows sum to one, and its
nontrivial eigenvalues lambda_i(M)/c lie in (0,1) with the same required
equalities. Thus A and every J(t) lie in the SAME original T_* class,
indeed in T_*^+. Direct multiplication gives K_B=M exactly.

**Theorem F.** For the maximal root-blob graph contract of Section 2 and
every fixed strictly positive original inheritance assignment, the exact
ordered (a,b) pair image is {(1/4)M : M in T_*^+}, separately for
*=J,2,3, even when the allowed original edge class is the literal T_*.

The two-edge rooted fork has exactly the same image. Necessity is the
two-factor support argument. For sufficiency, the same compensation with
any c in (max{0,lambda_max,1-4m},1) gives M=A J(c), with both fork matrices
in T_*^+. Thus the theorem compares the original full domains, not only
an approximation or their closures.

## 5. Full open H-equivariant class, with the D_mu convention

Let S be a finite state set of size at least two, and H any group of state
permutations. Allow ALL strictly positive row-stochastic matrices M with
M(hi,hj)=M(i,j), and freely varying H-invariant root distributions.
The root distribution may have zero entries. There is no embeddability,
fixed-root, shared-generator, reversibility or spectral restriction.

Let P_H^+ be the strictly positive probability tables J on S x S satisfying
J(hi,hj)=J(i,j). Rows are indexed by the state at a and columns by the state
at b. Diagonal matrices D_mu always use this row-marginal convention here.

### 5.1 Forward image, including root distributions with zeros

Fix any admitted parameters. Both a and b are distinct nonroot vertices.
For any requested pair of states i,j, choose a root state of positive root
probability and arbitrary states for the other hidden vertices, with a=i
and b=j. In any resolved tree all its transition factors are strictly
positive. This assignment contributes positively to the requested pair
probability. Thus every resolved table and their mixture are strictly
positive. Applying h to all assigned states preserves the root and edge
factors; summing preserves simultaneous H-invariance. Hence the resulting
table lies in P_H^+. No marginal-zero or terminal-independence assumption
is hidden in this argument.

### 5.2 Reverse image without commuting A past a reset

Fix J in P_H^+. Set

    mu_i = sum_j J_ij,
    M_ij = J_ij/mu_i,
    nu = mu M.

Then mu and nu are strictly positive invariant probability rows, M is
positive stochastic and equivariant, and J=D_mu M. Put

    E_mu(t)=tI+(1-t)1mu.

Use root mu, put A on every incoming-b edge, and E_mu(t) on all other
internal edges. The common reset satisfies

    mu E_mu(t)=mu,
    E_mu(s)E_mu(t)=E_mu(st),
    E_mu(t)^T D_mu = D_mu E_mu(t).

Since b is an internal sink, no A edge can be ancestral to a or to the
resolved lowest common ancestor of a,b. Thus that ancestor has law mu.
If its path to a has k reset edges and its path to the parent of b has
ell reset edges, then k+ell=L_sigma-1. Ordinary rooted-tree conditioning
gives the ordered table

    (E_mu(t)^k)^T D_mu E_mu(t)^ell A
      = D_mu E_mu(t)^(k+ell) A
      = D_mu E_mu(t^(L_sigma-1)) A.

This also handles a being the common ancestor (k=0), and the possible
one-edge a-to-b path (k=ell=0). Averaging gives

    J_B = D_mu E_mu(c(t)) A.                         (H1)

There has been no assertion that A commutes with E_mu(t). Only reversibility
and mutual multiplication of the reset factors were used.

Let alpha=min_ij M_ij/nu_j>0. Choose finite t<1 with 1-c(t)<alpha, and put

    A = [M-(1-c)1nu]/c,     c=c(t).                  (H2)

Every entry of A is positive. Its row sums are [1-(1-c)]/c=1, and it is
equivariant because M is equivariant and nu is invariant. Moreover

    mu A=[nu-(1-c)nu]/c=nu,
    E_mu(c)A=cA+(1-c)1(mu A)=M.

Equations (H1)–(H2) give J_B=D_mu M=J exactly, with the original inheritance
unchanged. Every edge remains in the original full open equivariant class.

**Theorem H.** Under the Section 2 graph contract, the exact ordered pair
image is P_H^+ for every fixed strictly positive original inheritance
assignment. The retained-port rooted fork has the same image: its necessity
is the same positive-assignment argument, and its sufficiency is this
construction with L=2 and c=t. Root parameters may change to mu; this is
not a fixed-root theorem except in the separate uniform-root group-based
cases already proved in Section 4.

## 6. Strictly positive-rate CT-K2P, not the rate boundary or CT-K3P

For completeness the same direct-port proof also composes the previously
reviewed CT-K2P-positive theorem without subdividing any cut edge. Its edge
class C2> has integrated rates a,b>0, uniform root, and eigenvalues x,x,y
with x=exp[-2(a+b)], y=exp[-4b]. Equivalently 0<x,y<1 and y>x^2.

On each resolved nonempty a-to-b path, products X_sigma,Y_sigma satisfy
Y_sigma>X_sigma^2. Hence the mixed eigenvalues satisfy

    y=sum w_sigma Y_sigma
      >sum w_sigma X_sigma^2
      >=(sum w_sigma X_sigma)^2=x^2.

This inclusion requires only L_sigma>=1, so one-edge paths cause no gap.
For a target (x,x,y) in C2>, use the same A/J(t) assignment and choose
c(t)>max{x,y,x^2/y}. The compensating A has eigenvalues x/c,x/c,y/c and
strictly positive integrated rates

    a_A=log(c y/x^2)/4,     b_A=-log(y/c)/4.

Every reset J(t) also has both integrated rates -log(t)/4>0. Thus the target
is attained in the same original C2> class. The rooted fork has exact image
C2> because these commuting generators add and each positive rate pair
splits into two positive halves. This proves both local image directions.

No zero rate is included. The earlier positive-entry/zero-rate K2P failure
and positive-rate K3P mixture obstruction remain unchanged. In particular
the latter does not satisfy the convex-path inclusion just used for K2P.

## 7. Complete observed-law equality with fixed original cut matrices

Write the two original cut edges as a->c_a and b->c_b. Define F with vertex
set (V(G) minus B) union {a,b,rho}, where rho is fresh. Remove EVERY original
edge with both endpoints in B, including a->b if present, and add precisely
rho->a and rho->b. Keep all original edges whose target lies outside B,
their original occurrences, and the exterior observations. In particular
both cut-edge occurrences a->c_a and b->c_b remain unchanged. The
rooted fork's two new incoming weights are 1, since each port now has just
one parent. Deleted interior edge IDs and weights are not asserted to
survive as new fork edge IDs.

Fix any allowed exterior parameter assignment theta_ext, including BOTH
cut matrices, all other exterior matrices, and all parent-choice vectors
at exterior vertices. Fix any allowed positive normalized original
inheritance assignment W_B inside B. Its choices are independent of the
exterior choices. There is no incoming boundary edge and no observation
inside B. Thus the unchanged exterior defines one stochastic kernel

    Q_theta_ext(z | i,j)

from the ordered port states to the full labelled observation z. This
kernel can be obtained by the finite product of exterior conditional
factors followed by summation over all exterior hidden states. Its
dependence on internal B states is only through a,b. External reconvergence
or additional parent terms do not license replacing a joint table by its
marginals, and no such replacement is used.

For both networks the full observed probability is exactly

    p(z)=sum_ij P_ab(i,j) Q_theta_ext(z | i,j).

For each of the domains in Theorems F and H and Section 6:

* Starting from any original G parameter point, its port table belongs to
  the classified pair image. The rooted fork realizes that same table.
  Leave theta_ext unchanged. The complete observed law is identical.
* Starting from any fork F parameter point, its port table belongs to that
  same image. The construction in the ORIGINAL blob realizes it with the
  originally prescribed W_B, not new or limiting inheritance. Leave
  theta_ext unchanged. Again the complete observed law is identical.

Consequently the two observed-law images are equal for EVERY fixed common
theta_ext and EVERY fixed allowed W_B. In Theorem F the fixed exterior
Fourier matrices may themselves contain zero entries. In Theorem H they
are strictly positive, as required by that original domain. In Section 6
they have strictly positive K2P rates. The construction does not alter any
of them. Interior edge matrices remain freely and independently variable;
constraints coupling them to protected exterior matrices are not covered.

## 8. Precise exclusions and remaining trust dependencies

This is a stronger retained-port hand theorem, not a retraction of the
previous free-cut subdivision theorem. In particular:

* It does not turn a zero-entry K2P/K3P matrix into a product of two literal
  domain matrices. The support argument proves that such a product is
  impossible. No individual zero-entry cut factorization is used here.
* It does not assert equality with an unrestricted single semidirected
  replacement edge or with all possible root placements. The published
  quartet boundary counterexample still has exactly its earlier force.
* It does not preserve a prescribed open-equivariant root parameter or
  fixed original interior matrices. For Fourier and CT-K2P the root remains
  uniform throughout, as specified by those domains.
* It does not cover arbitrary smaller equivariant families, shared edge
  matrices/generators, fixed branch lengths, zero-rate CT-K2P or CT-K3P
  model-image equality.
* It does not justify the literal broader root-trapping 2-sub-blob operation
  or its universal semidirected larger-blob root lift. The maximal actual
  root-containing graph contract remains explicit.

The whole hand claim depends on the graph facts in Section 2, the actual
shared-selector path marginalization in Section 3, the domain-specific
forward and reverse proofs in Sections 4–6, and the joint-context identity
in Section 7. None is replaced by a conditional algebra lemma alone.
The prior two-sink and maximal-subdivision source proposals remain
UNELABORATED; this note adds no Lean code or execution. The new direct-port
argument has not been formalized. Historical priority remains bounded by
the existing primary-source review, not certified worldwide novelty.
