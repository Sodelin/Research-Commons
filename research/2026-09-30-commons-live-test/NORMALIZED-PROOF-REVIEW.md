# Independent reconstruction of the normalized global proof

2026-09-30 UTC. Omnibus-audit chat. This is deliberate independent review of the catalog chat's reported result, not a priority claim or a review of its unseen final text. It inherits the accepted computer-assisted local theorem and original composition in Samuel commit `e2502c82ab9a77c00543932f775a71e5374221f7`. It is not Lean checked.

Inherited inputs: [all-level proof, especially Theorem B and §7](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-PROOF.md) and [composition audit, especially §4–5](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-COMPOSITION-AUDIT.md). The baseline was read, not re-proved in this lane.

## Claimed normalized result

For real c,a with s=o=1, universal circular decomposability on the declared finite binary semi-directed LSA-rootable, outer-labeled planar, galled class with at least four taxa is exactly

```
0<=c<=1, (1+c)/2<=a<=1.
```

### Sufficiency: cherry-zero composition and star normalization

Write d_b=d(0,1,b,1). Relative to original NANUQ d_(1/2),

```
d_b(x,y)=d_(1/2)(x,y)+(2b-1) A_N(x,y),
```

where A_N counts auxiliary pairs whose distinct quartet set has two topologies and the queried pair is adjacent. If a cut edge resolves a quartet, it has one topology and contributes zero to A_N. Otherwise its four leaves occupy four distinct ports of the unique central blob of the restricted blob tree. Its topology set, and hence the adjacency classification, equals that of the capped local blob. Counting the two auxiliary taxa gives the factors m(p)m(q). Thus the correction localizes exactly, including zero contribution when the queried taxa project to the same port.

Adding this to accepted original composition proves the identical blob composition for d_b at every real b. Ordinary trivalent vertices keep their original endpoint terms; two-port blobs stay zero. No new level bound is used. When 1/2<=b<=1, the accepted weighted local anchor theorem supplies nonnegative local split coefficients. Positive port masses and contiguous port components lift them into one global circular order. This discharges positivity for d_b using the declared source class, rather than assuming a parameter composition for c>0.

For 0<=c<1, set b=(a-c)/(1-c). The score conditions make 1/2<=b<=1, and the exact global identity is

```
d(c,1,a,1)=c*star[K_n]+(1-c)*d_b,
K_n=(n-1)(n-2).
```

Both coefficients are nonnegative; the star is circular in every order. At c=1 the region forces a=1 and the distance is pure star. This proves sufficiency relative to the accepted baseline local/structural/composition inputs. It does not silently reuse the old composition for c>0.

### Necessity: every-order obstructions

**c<0.** In a binary tree with a cherry x,x', every auxiliary quartet scores c for that pair, so d(x,x')=2n-4+c(n-2)(n-3). For sufficiently large finite n this is negative.

**c>1.** A five-taxon tree with cherry x,x' and three outsiders has d(c)=c*star[K_n]+(1-c)*d_original. Every quartet x,x',y,z then uniquely maximizes d(x,x')+d(y,z), because the original tree strictly minimizes that sum. Any compatible circle would place every pair among the three outsiders on opposite arcs of x,x', which is impossible. The exact five-taxon matrix and all twelve orders were checked independently.

**a>1 with 0<=c<=1.** The delivered independent [sunlet argument](a-boundary/UPPER-RESULT.md) uses one fixed chord that must cross all three edges of an outsider triangle. Its exact quartet-sum comparisons are strictly signed for a sufficiently large admitted sunlet. The c<0 case was already excluded. This is an every-order argument; a four-taxon negative embedding coefficient alone would not suffice.

**a<(1+c)/2 with 0<=c<1.** Set b=(a-c)/(1-c)<1/2. Use a sunlet with r=2k+1 ordinary leaves in path order, replacing its hybrid leaf by a cherry x,x'. Let u,v be the two endpoints of the ordinary path and z its middle leaf, with k ordinary leaves on each side. The total taxon count is n=2k+3. Require k>=2.

Here is an all-size counting derivation. In the table, C(t,2)=t(t-1)/2. Columns count unordered auxiliary pairs in each score category; each row sums to C(r,2). The two twins are interchangeable, and reversal exchanges u,v.

| Queried pair | Cherry c | Separated s | Adjacent a | Opposite o |
|---|---:|---:|---:|---:|
| x,x' | C(r,2) | 0 | 0 | 0 |
| x,u or x,v | 0 | r-1 | C(r-1,2) | 0 |
| x,z | 0 | r-1 | C(r-1,2)-k^2 | k^2 |
| u,v | 1 | C(r-2,2) | 0 | 2(r-2) |
| u,z or v,z | 1+C(k,2) | C(r-2,2)-C(k,2) | 2k | 2(k-1) |

For x,x', every auxiliary pair is ordinary and the queried twins form a cherry. For x,u or x,z, auxiliary pairs containing x' give r-1 resolved, separated quartets; all other auxiliary pairs consist of ordinary leaves. At endpoint u all those ambiguous quartets are adjacent. At z exactly k^2 pairs straddle z, making the queried pair opposite.

For a queried pair of ordinary leaves, the auxiliary pair of both twins makes that queried pair a cherry. Exactly one twin and one other ordinary leaf gives a sunlet quartet, with two choices of twin. For u,v all 2(r-2) are opposite; for u,z the k ordinary leaves beyond z give 2k adjacent quartets and the k-1 between u,z give 2(k-1) opposite quartets. Finally, two ordinary auxiliary leaves give a quartet of the ordinary caterpillar: u,v are always separated, while u,z form a cherry precisely when both auxiliary leaves lie beyond z, in C(k,2) cases. These cases partition the auxiliary pairs for every k and give the displayed table without interpolation.

Substituting (c,s,a,o)=(0,1,b,1), multiplying the score sum by 2 and adding the baseline 2n-4=2r gives

```
d_b(x,x')=2r
d_b(x,u)=d_b(x,v)=4r-2+b(r-1)(r-2)
d_b(x,z)=d_b(x,u)+2(1-b)k^2
d_b(u,v)=r^2+r-2
d_b(u,z)=d_b(v,z)=3k^2+3k+4bk.
```

Write T(y,z)=d(x,x')+d(y,z)-d(x,y)-d(x',z). The twins have identical outsider distances. Therefore

```
T(u,v)=4(1-2b)k^2+(4b-6)k-2,
T(u,z)=T(v,z)=(1-6b)k^2+(8b-9)k-2.
```

Choose an integer k>=2 with k>(8-4b)/(4(1-2b)). This makes T(u,v)>0: its quadratic coefficient times k exceeds 6-4b+2, leaving a value greater than 2k-2. If 1/6<=b<1/2 the other two contrasts are negative, since their quadratic coefficient is nonpositive and their linear coefficient is negative. If b<1/6 also choose k>(11-8b)/(1-6b); the same argument makes the other two contrasts positive. In either case all contrasts are nonzero and the number of positive signs is odd.

For a circular split sum, its crossing four-taxon pairing attains a largest pair sum. Distance-twin equality makes the two non-twin pair sums equal. Consequently positive T forces the twin pairing to cross (outsiders on opposite arcs), while negative T rules that crossing out (outsiders on the same arc). No assignment to two arcs has the odd-positive triangle. Star normalization multiplies all four-point contrasts by 1-c>0, so the original score vector has the same obstruction, including the nonnegative source subdomain. The intermediate b need not be a nonnegative score.

**c=1,a<1.** With all nonadjacent categories equal to 1, the same table gives d(x,y)=K_n+2(a-1) times its adjacent-pair count, hence

```
T(u,v)=2(1-a)(r-1)(r-2),
T(u,z)=T(v,z)=2(1-a)k(3k-4).
```

Choose k=2. All three are positive, again excluding every circle.

The family remains binary, LSA-rootable, outer-labeled planar and galled when ordinary path leaves are added or the hybrid taxon is replaced by a cherry. The original rooted LSA witnesses in separate root branches remain; the hybrid has a pendant outgoing cut edge. This is source admission for every finite k, not extrapolation from a fixed graph screen.

## Review status

This reconstruction supplies a source-compatible unbounded mechanism for the reported normalized theorem. A [fresh internal adversarial review](INDEPENDENT-REVIEW.md) independently derived its count table and found no unresolved gap conditional on the inherited inputs. The 32 [finite lower-bound controls](lower-count-review.json) corroborate the counting formulas; they are not the all-size proof. The [tree upper-bound checker](tree_boundary_review.py) supplies three exact five-taxon controls with all 12 orders rejected each. Local positivity, original composition, and source representation inherit their recorded computer-assisted verification level. Full end-to-end Lean verification, support extension, freely varying opposite score, biological estimation and author priority are outside this review. The owner's actual proof/checker still needs direct comparison before an audit of that canonical package can be declared complete.
