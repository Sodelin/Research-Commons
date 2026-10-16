# A retained-count bound for arbitrary supplied residue nodes at the codimension-one cap

Contributor: dot, 16 October 2026. Status: candidate hand proof for review. This is a supplied-node necessary boundary restriction, not an original-input witness bound. No QE, source solver, compilation, or numerical cutoff was executed.

## Main result and relation to the master gap

Fix s>=1 distinct nodes Q={r_1,...,r_s} in (0,1), and cap M=2s+5, so d=M-1=2s+4. Use the d positive Kingman exponents. Let rho=min Q. Consider any supplied COMMON closure normal form

h=a Lambda+sum_i H(p_i,q_i)+sum_(j=1)^s w_j R(r_j),

a>0, w_j>0, 0<p_i,q_i<1, H_lambda(p,q)=-log(1-p+p q^lambda), R_lambda(r)=(1-r^lambda)/(1-r).

There is no killing term. The retained list may initially be finite or countably summable. Then there exists epsilon(Q)>0 such that, if h is not attained by a finite strict source, every retained factor satisfies

p_i(1-q_i)>=epsilon(Q).

Consequently the list is finite and N<=h_1/epsilon(Q). For effectively algebraic supplied nodes and effectively algebraic m_1=exp(-h_1)>0, an integer bound on N is computable by finite real-algebraic decisions and elementary rational comparisons. No small-loss restriction is needed.

The accepted enhanced-rank theorem already gives the common retained-factor annihilator. The proposed extension is a general fixed-normal critical-loss lemma that handles every finite collection of exact double roots, including cubic contacts. It extends the existing supplied single-node/dyadic retained-count argument to arbitrary supplied node configurations at this codimension-one cap. It does not acquire Q from the original observation input, bound the minimum number of factors in an attained fibre, or classify the remaining bounded exceptional images. General G3 and General G4 remain separately open.

## 1. Fixed-normal lemma

Let lambda_1,...,lambda_d be distinct positive integers, c a nonzero real row, and

F(x)=sum_j c_j(1-x^lambda_j), L(p,q)=sum_j c_j H_lambda_j(p,q).

Assume F(0)!=0, F has a double root at 1, and every root of F in (0,1) has exactly multiplicity two. Then there is epsilon(c)>0 such that every strict simultaneous critical pair L_p=L_q=0 satisfies p(1-q)>=epsilon(c).

No positivity sign for F or for its intermediate power values is needed for the local argument. In the application F is positive away from its prescribed roots, but the lemma only uses their exact multiplicities and a nonzero first missing value.

### Interior rare-event corner

Suppose critical pairs approach p=0,q=q0 in (0,1). Since L_p(0,q)=F(q) and lim_(p->0) L_q/p=F'(q), the limit must satisfy F(q0)=F'(q0)=0. By hypothesis F''(q0)!=0.

Use z=p/(1-p); for z near zero the analytic identity is

L(z,q)=sum_(j>=1) (-1)^(j+1) z^j F(q^j)/j.

Criticality in p is equivalent to criticality in z because dz/dp>0. Let k>=2 be the first positive integer for which F(q0^k)!=0. Such k exists: q0^j are distinct and tend to zero, and F has finitely many roots with F(0)!=0. For j<k, each q0^j is an interior double root, so F(q^j)=O((q-q0)^2) and its q derivative is O(q-q0), uniformly in a fixed neighborhood. The analytic series and its first derivatives have uniform remainders there.

Write delta=q-q0. Dividing L_q=0 by z gives

0=delta[F''(q0)+O(delta)+O(z)]+O(z^(k-1)).

The bracket stays bounded away from zero. Therefore delta=O(z^(k-1)). Now the other critical equation gives

0=L_z=(-1)^(k+1) z^(k-1) F(q0^k)+O(z^k).

Indeed all j<k terms are O(delta^2), which is O(z^(2k-2))=O(z^k) because k>=2; variation of the kth coefficient contributes O(z^(k-1)delta), also O(z^k); and the differentiated tail starts at order z^k. The displayed leading coefficient is nonzero, a contradiction for z>0 sufficiently small. Its parity affects only its sign and cannot remove the contradiction.

Thus no strict critical sequence can approach any interior rare-event corner. This is precisely why cube separation was unnecessary for the critical-loss conclusion even though it mattered to the older two-normal signed budget.

### Endpoint q=0

If p->0,q->0, then L_p->F(0)!=0 by continuity of the finite rational derivative formula. Such a sequence is not critical.

### Endpoint q=1, uniformly in p

Near the compact interval p in [0,1], q=1, every logarithm argument is uniformly positive. Since c.Lambda=0 from F'(1)=0, L vanishes at p=0 and p=1; it also has a double zero at q=1. Analytic division gives

L=p(1-p)(1-q)^2 A(p,q), A(p,1)=F''(1)/2!=0.

Both A and A_q are uniformly bounded, and A is uniformly bounded away from zero for q near 1. Therefore

L_q=p(1-p)(1-q)[-2A+(1-q)A_q]

is nonzero for every strict p and q sufficiently close to 1. This covers simultaneous p approaching 0 or 1.

### Compactness conclusion

If no positive critical-loss floor existed, choose strict critical pairs with p(1-q)->0 and a convergent subsequence in [0,1]^2. Its limit has either p=0 or q=1. The q=1 case is excluded uniformly. The p=0 cases are exactly the two remaining analyses above, including the possibility of nonroot q0, which already contradicts the limiting derivatives. Hence a positive epsilon exists. An empty strict critical set is harmless: any positive epsilon satisfies the assertion.

## 2. Why the application has exactly this fixed normal

Use the accepted enhanced residue/retained-factor criterion. For a nonattained normal form, one common nonzero c annihilates

Lambda; R(r_j), R'(r_j) for every j; D(rho^2), D'(rho^2); and H_p,H_q at every retained pair,

where D(x)=1-x^Lambda. Positive weights can be removed from the derivative columns as nonzero scales. Since rho^2<rho, S=Q union {rho^2} has exactly s+1 nodes.

The first d-1=2s+3 columns have rank d-1. Equivalently their normal polynomial has double roots at 1 and every element of S, a total of 2s+4=d roots counted with multiplicity. There is a nonzero solution by dimension count. Two independent solutions could be combined to cancel their constant term; the resulting polynomial would have at most d nonzero monomials and thus at most d-1 positive roots by sparse Descartes, a contradiction. The same reasoning excludes a zero constant term in a nonzero solution. Normalize F(0)=1.

A polynomial with at most d+1 monomials has at most d positive roots counted with multiplicity. The prescribed roots already use all d, so each has exactly multiplicity two and there are no other positive roots. In particular F''(1)!=0 and the fixed-normal lemma applies. The normal is unique up to scale, so every nonattained representation with these same nodes uses this same strict critical locus for all retained factors. This is a consequence of the accepted full-column rank criterion, not an arbitrary choice of a separator.

The critical-loss floor gives

N epsilon <= sum_i p_i(1-q_i) <= sum_i H_1(p_i,q_i) <= h_1.

An infinite summable retained list is therefore impossible on this stratum. This argument concerns all its retained pairs simultaneously, and does not replace integer multiplicities by continuous weights.

## 3. Effective supplied-node extraction

If every r_j is effectively real-algebraic, rho and rho^2 are effectively algebraic and the unique normalized coefficient row c is computable by finite algebraic linear algebra. The strict critical equations are rational functions with positive denominators D_lambda=1-p+p q^lambda on (0,1)^2. Clear these denominators, obtaining exact polynomial equations over the real-algebraic coefficient field.

For n=1,2,... decide by real-closed-field quantifier elimination whether there exists a strict critical pair with p(1-q)<2^(-n). The lemma proves that eventually the answer is false. Set epsilon=2^(-n) at the first such answer. This is an effective terminating search for this fixed supplied node tuple; no claim of a practical runtime or a uniform n as nodes vary is made.

Given algebraic m_1 in (0,1), find an integer b>=1 with m_1>2^(-b) by exact algebraic comparison. Then h_1=-log m_1<b log 2<b. A valid computable integer bound is floor(b/epsilon). Every nonattained normal form with these supplied nodes has at most that many retained factors. If a supplied representation exceeds the bound, it must be attained; the enhanced criterion in fact forces a noncritical retained derivative and therefore interior attainment.

This last conclusion is an existence statement. A strict finite witness can then be found by the existing fair fixed-graph/source enumeration under its algebraic observation-input contract, but neither that witness nor an execution time is produced here.

## 4. Exact remaining gap

This bound is for retained factors in a nonattained closure representation with supplied nodes. It is not a bound on actual YES witnesses. A short exceptional representation could still admit a different large strict realization. Original G3 does not supply a residue list; arbitrary inputs can have different numbers of residues, active killing or zero-drift flags, and higher-dimensional normal spaces. The present result does not acquire those data or classify attainment on the bounded exceptional set.

The result therefore removes cube-contact concerns from this specific retained-count proof, but does not establish the input-effective one-witness bound required by the original master problem. No extension by subtracting a retained head is valid: the accepted interior-absorption theorem allows such heads to convert nonattained closure tails into attained total signatures.

## Sources, prior delta, and verification

- [Enhanced retained-rank criterion](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-01-sol61-g3-boundary-resume-2124z/ENHANCED-RETAINED-RANK-CRITERION.md): accepted all-normal-form annihilator and interior criterion used in Section 2.
- [Supplied single-residue critical count](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-01-sol61-g3-boundary-resume-2124z/SUPPLIED-RESIDUE-CRITICAL-COUNT-BOUND.md): prior effective fixed-node reduction.
- [Dyadic critical exceptional stratum](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-01-sol61-g3-boundary-resume-2124z/DYADIC-CRITICAL-EXCEPTIONAL-STRATUM.md): earlier general dyadic count/finite-level extension; its captured full-review status is separate.
- [Neutral accumulation theorem](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-01-sol61-g3-boundary-resume-2124z/NEUTRAL-ACCUMULATION.md): already excludes q=1 for every fixed covector and reduces remaining critical tails to rare-event double roots. The present lemma adds exclusion when every interior root is exactly double and the finite first-missing-power argument applies.
- [Exact retained-tail compression](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-01-sol61-g3-boundary-resume-2124z/EXACT-TAIL-COMPRESSION.md): finite retention was already known existentially in broader scope. It did not supply this computable fixed-node count floor.

The local derivative argument, general supplied-node composition, and effective search are submitted for hand review. Historical novelty is unresolved. No calculation or proof assistant execution is claimed.

## Scoped hand-review record, 16 October 2026

The coordinating dot reviewer independently read the complete proof and the pinned enhanced-rank supplier and communicated scoped HAND PASS. The review checked the L_q/z displacement bound, every lower-order and kth-term remainder in L_z including k=2, both endpoint arguments, the saturated root/rank count, termination of the QE floor search, and the elementary h_1 bound. This is mathematical source/manual review; no solver execution, numerical certificate, historical novelty acceptance, or general G3/G4 closure is asserted. The supplied-node and nonattained-representation restrictions above remain essential.
