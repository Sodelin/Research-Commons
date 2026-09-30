# Independent all-order validation of a <= 1

Status: hand-derived argument independently checked algebraically. This is
deliberate independent validation, not a novelty claim: the external catalog
chat reported owning and solving necessity before this lane was integrated.
Root requested that further searches stop, and no additional search follows.

Contributors: source-boundary session and its a_upper_review sub-agent. The
sub-agent supplied the final three-chord obstruction; the session checked
the pair-sum differences and inequalities.

Fix s=o=1, 0<=c<=1, and suppose a>1. Write delta=a-1>0 and b=1-c>=0.
Use the admitted plain (m+1)-sunlet with hybrid leaf h and ordinary leaves
1,...,m around the cycle. Subdivide the ordinary 1--2 cycle edge with a root
and orient both cycle paths toward the sole hybrid. The two ordinary leaves
1,2 remain witnesses in different root branches, so the root is the LSA.
Every tree vertex is binary; the hybrid's outgoing pendant edge is a bridge.
The cycle with its pendant leaves is outer-labeled planar and galled.
Suppressing the root gives the required semi-directed network at every m.

Let B=2(m+1)-4, T=binom(m-1,2), and for 1<=i<j<=m define

    P_i = (i-1)(m-i),
    C_ij = binom(i-1,2)+binom(m-j,2).

Direct distinct-quartet counts give

    d(h,i) = 2[aT+(1-a)P_i]+B,
    d(i,j) = 2[binom(m-2,2)+(c-1)C_ij
                 +a(m-1-j+i)+(j-i-1)]+B.

For 1<=i<j<k<=m, put

    D1 = d(h,i)+d(j,k),
    D2 = d(h,j)+d(i,k),
    D3 = d(h,k)+d(i,j).

Expanding the counts yields

    D1-D2 = (j-i)[2 delta(m+2-i-j)-b(i+j-3)],
    D2-D3 = (k-j)[2 delta(m-j-k)+b(2m-j-k-1)].

Choose

    m = max(7, 3+floor[b/(2 delta)]).

Then m>=7 and delta(m-2)>b/2. Set i=1 and take (j,k) from
(2,3),(2,4),(3,4). The first difference is strictly positive in each case:
for j=2 it is 2 delta(m-1), and for j=3 it is
2[2 delta(m-2)-b]. The second difference is nonnegative because
m-j-k>=0 and 2m-j-k-1>=0. Consequently D1 is the unique largest of
the three pair sums for each of these three four-taxon subsets.

For a nonnegative circular split metric, the crossing pairing of each four
taxa attains a largest pair sum. This follows termwise for circular split
metrics, then by addition. A unique maximum therefore forces that pairing
to be the crossing pairing in every circular representation.

Here every circular representation would require chord h--1 to cross each
of 2--3, 2--4 and 3--4. The three taxa 2,3,4 would therefore have to lie
pairwise on opposite arcs determined by h,1. Two arcs cannot accommodate
three points with that property. Thus no circular representation exists.

This proves universal aggregate circularity forces a<=1 within 0<=c<=1.
It uses a larger source-admitted family and all circular orders, not a
negative coefficient in the source embedding order.

Earlier bounded symbolic sunlet screens were discovery evidence and are not
needed by this unbounded hand argument. No additional graph computation was
run in this upper-necessity lane after the root stop request.

Source correspondence: NANUQ+ Definition 3.1 allows arbitrary nonnegative
scores. Section 3 expressly does not claim precise combinatorial structure
for other family members; Lemma 3.5 proves signs of relative distances on
sunlets, not universal circularity necessity. Holtgrefe Section 6 mentions
parametric extension without adding score bounds. No additional literature
survey was performed in this mathematical lane.
