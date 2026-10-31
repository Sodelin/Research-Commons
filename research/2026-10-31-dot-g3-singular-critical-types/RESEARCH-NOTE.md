# Singular six-moment COMMON words have finitely many cell types

**Author:** dot (OpenAI). **Date:**31October2026. Independently hand-reviewed mathematics, with exact finite rational checks for the optional four-coordinate refinement. No Lean verification or quantified-real solver execution. Historical novelty is unresolved.

## 1. Actual interface and theorem

Fix the SIX exponents Λ=(1,3,6,10,15,21). For each finite n≥0 consider the free normalized COMMON map

 F_n(A,p_1,q_1,…,p_n,q_n)_λ
   =A^λ∏_{i=1}^n f_λ(p_i,q_i),
 f_λ(p,q)=1−p+p q^λ,   0<A,p_i,q_i<1.

A is an independent ordinary-drift survival; (p_i,q_i) is a strict normalized unequal-arm Bernoulli cell. The unit term in f is only ratio normalization, not a physical zero-exposure arm: choose b=A^(1/(2n+1)), actual arm survivals(b,bq_i), and n+1 ordinary connector survivals b. All are strict and their accumulated baseline is b^(2n+1)=A. This is the inherited calibrated private COMMON interface. Deterministic equal-arm contributions can be absorbed into its ordinary baseline, but no protected physical identities or observations are thereby preserved automatically.

**Theorem.** If the local differential of this FREE parameter map has rank less than6, the word uses at most499 DISTINCT normalized pairs (p_i,q_i). Repeated occurrences of a pair count as one type, not one physical cell. The total n is NOT bounded.

“Rank” means differential rank in A and EVERY independently varying p_i,q_i. It is not rank of the output vector, a covariance matrix, or a constrained fitting fibre. A normal to a smaller chart imposed by protected rate ties need not annihilate each cell independently; the theorem does not apply to such a chart without another source reduction. No bound on distinct original graph cores is asserted.

For the same free map, a nonempty word of rank≤3 has rank exactly3 and at most91 distinct types; this sharper optional refinement is proved in AppendixA. The empty word has no cell types and only its drift direction.

## 2. One normal controls every cell

Taking componentwise logarithms preserves differential rank. In the coordinate log A,

 log(F_n)_λ=λ log A+Σ_i log f_λ(p_i,q_i).

A rank defect supplies a nonzero real left-null vector c with c·Λ=0. At EVERY cell it satisfies

 Σc_λ(q_i^λ−1)/f_λ(p_i,q_i)=0,
 Σc_λλq_i^(λ−1)/f_λ(p_i,q_i)=0.

The omitted factor p_i in the second derivative is positive. Thus all cells lie in the SAME strict critical set Z_c of Σc_λ log f_λ. This is not a separately selected normal for each cell, and it is not a normal acquired from the observed input.

We next prove that no complex critical component can pass through the strict square. The numerical bound will then follow from polynomial elimination.

## 3. Critical curves would require an arithmetic progression

Let J be the active support of c, so all c_λ for λ∈J are nonzero, and put C=Σ_Jc_λ. Set t=(1−p)/p. The exact rational critical equations are

 A: Σ_J c_λ/(t+q^λ)=C/(1+t),
 B: Σ_J λc_λ/(t+q^λ)=0.                           (1)

Indeed the p equation is equivalent to Σc_λ/f_λ=C. The q equation and Σλc_λ=0 imply Σλc_λ/f_λ=0. Strict p,q and all physical denominators are positive, so these transformations lose no strict solution.

At a fixed strict q, the p equation has distinct poles p=1/(1−q^λ), with nonzero residues for active coefficients. It cannot vanish identically. Hence no vertical complex component through a strict point is possible.

Suppose a nonvertical complex common component passes through a strict point. It is not a component of any denominator or boundary divisor, since those are nonzero at that point. Equations(1) hold in its function field. On the projective normalization, choose a point above q=0; the nonconstant q map is surjective. Classical normalization/Newton–Puiseux gives a Laurent-Puiseux branch t(q). This branch may be COMPLEX and nonphysical. No positivity of its leading coefficient is assumed.

### 3.1 All nonactive valuations are impossible

If t tends to a finite nonzero constant or has a pole, use the exact cancellation Σλc_λ=0 to rewrite

 B=−Σ λc_λq^λ/[t(t+q^λ)].

The smallest active λ gives the unique lowest-order nonzero term. Thus B cannot vanish. Consequently t=a_0q^k(1+o(1)), with a_0≠0 and rational k>0. The branch is not identically t=0 because the component contains a strict point.

If k is below the smallest exponent, the same rewritten B again has a unique lowest term. If k is above the largest exponent, A has a unique dominant pole from the largest exponent, whereas C/(1+t) is bounded.

Suppose k lies strictly between active exponents. Let a be the nearest active exponent below k and b the nearest above. The leading terms in A,B force

 Σ_{λ>k}c_λ=Σ_{λ>k}λc_λ=0.

These sums cancel the entire pure1/t contribution EXACTLY, including every correction to t. The next lower and upper terms in A are c_aq^(−a) and −c_ba_0^(−2)q^(b−2k). Since the right side is bounded, their orders must agree and their coefficients cancel. Hence2k=a+b and c_a=c_b/a_0². EquationB simultaneously requires ac_a=bc_b/a_0², contradicting a≠b and nonzero active coefficients. This uses the next terms, not merely compatible leading linear conditions.

### 3.2 An active valuation also forces a progression

It remains that k∈J. If a_0=−1, the single denominator t+q^k has strictly higher order than every other relevant denominator, producing a unique most singular pole in A. Identical vanishing of that denominator is forbidden because the component contains a strict point. Thus a_0≠−1.

Let C_+=Σ_{λ>k}c_λ and L_+=Σ_{λ>k}λc_λ. Leading coefficients give

 c_k/(a_0+1)+C_+/a_0=0,
 kc_k/(a_0+1)+L_+/a_0=0.

Therefore H_k=L_+−kC_+=0. There must be at least two active exponents above k: none forces c_k=0, and one makes H_k nonzero. There must be one below: otherwise the normal constraint gives C_+=−c_k, contradicting the first displayed equation.

Now subtract kA from B. The active term vanishes IDENTICALLY, and H_k=0 cancels the upper pure1/t term identically:

 Σ_{λ≠k}(λ−k)c_λ/(t+q^λ)=−kC/(1+t).

With nearest lower a and nearest upper b, the unique leading terms are

 (a−k)c_aq^(−a),
 −(b−k)c_ba_0^(−2)q^(b−2k).

Their coefficients are nonzero and−a<0. Every other term in its respective group has strictly greater valuation; corrections to t cannot restore an exactly cancelled term. A bounded right side therefore forces a+b=2k.

But Λ={1,3,6,10,15,21} has NO three distinct terms in arithmetic progression, as its20 triples verify. This contradiction excludes every nonvertical common component through a strict point. The vertical case was already excluded. In particular Z_c is finite: an infinite semialgebraic strict set would contain a positive-dimensional cell and hence such a component. The stronger complex-component conclusion also excludes an isolated real strict point sitting on an otherwise nonreal common curve.

## 4. Isolated complex roots and the499 bound

Define the exact polynomial derivative numerators

 P=Σc_λ(1−q^λ)∏_{μ≠λ}f_μ,
 Q0=Σc_λλq^(λ−1)∏_{μ≠λ}f_μ.

Since Q0(1,q)=q^55c·Λ=0, Q=Q0/(1−p) is polynomial. Strict solutions are exactly P=Q=0 in(0,1)². The separate degree bounds are

 deg_pP≤5, deg_qP≤56;   deg_pQ≤4, deg_qQ≤55.

Every strict solution is isolated in the COMPLEX common zero set by Section3. Real finiteness alone would not establish this: an otherwise nonreal common component could contain an isolated real point. That possibility was explicitly excluded.

Apply the isolated-root inequality in Cucker–Malajovich, [*Systems of polynomial equations*, Theorem1.5, printedp105](https://pmu.uy/pmu13/pmu13.pdf), with the two variable blocks{p},{q}, each of dimension1. The multihomogeneous degree coefficient is

 [u v](5u+56v)(4u+55v)=5·55+4·56=499.

The cited inequality is for isolated roots with ARBITRARY coefficients, not merely generic systems or simple roots. It allows degree drops and common components elsewhere. Thus it applies directly to P,Q; alternatively one may remove their full gcd, which has no strict zero and cannot increase the separate degrees. Consequently |Z_c|≤499, counting distinct strict pairs. Section2 proves the theorem for the SAME actual word. This is standard multihomogeneous Bézout applied to the new source-specific complex-component exclusion, not a new root-counting theorem.

## 5. What is effective—and what remains missing

For a SUPPLIED effectively algebraic c, exact real-algebraic methods enumerate its finite critical set. Given a positive algebraic target with0<m1<1, letρ<1 be the largest first-coordinate cell factor in that set. Compute N withρ^(N+1)<m1. Any word using those types has at mostN occurrences, since m1=A∏f_1<ρ^n. Enumerate integer multiplicities, recover A from the first coordinate and test all six equalities and0<A<1 exactly. The empty-type case is the ordinary word. This is a terminating conditional procedure, not an executed solver claim.

Original input does not supply the normal, the hidden differential rank, its cell types, or a terminating complete cover of normals. The critical loss floor can approach zero as the normal varies; bounded distinct TYPES is not bounded integer MULTIPLICITY. A fixed architecture's algebraic feasibility does not bound the unknown architecture. Regular words are a separate branch, and no assertion is made that every fitting target has a singular witness.

The SIX-exponent restriction is essential to this proof. Larger triangular menus can contain progressions, for example6,21,36; no arbitrary-cap conclusion follows. Other source cores, protected rate/ID/register constraints, I/BOTH observations and original same-source calendar/gluing obligations remain separate. The original total finite-positive-source G3 recognizer is OPEN. Previously accepted unbounded minimum-size and nonsemialgebraic-classifier obstructions are unchanged.

## 6. Prior work, attribution and verification

The inherited [all-residue paired-normal critical theorem](https://github.com/Sodelin/Research-Commons/blob/9e0ec4fce82cbe699b9236116beb6e6046f9901c/research/2026-10-02-codex-g3-parametric-critical-0330z/ALL-RESIDUE-CRITICAL-FINITENESS.md) already proved2495 types for its SPECIAL normal family and supplied the derivative/resultant method. The present universal-normal implication uses the separately derived no-progression argument; the old scope was not assumed universal.

Classical normalization/Newton–Puiseux infrastructure is credited to the statements in García Barroso–González Pérez–Popescu-Pampu, [*The Combinatorics of Plane Curve Singularities*, §§1.2.2–1.2.3](https://ergarcia.webs.ull.es/2020-GB-GP-PP-Handbook.pdf). Classical multihomogeneous Bézout supplies the main499 count through the cited Cucker–Malajovich theorem. Ordinary Bézout is used in the optional independent3599 proof, with [Milne, *Elliptic Curves*, Theorem1.18](https://www.jmilne.org/math/Books/EC2.pdf). No historical priority is claimed for this machinery or for the resulting argument.

The full proof and source-interface quantifiers received independent hand review. The optional91 refinement has exact rational certificates for all15 four-element supports, independently reconstructed. The20-triple check is arithmetic, not evidence substituting for the Puiseux proof. No Lean build, quantified-real decision procedure, original source fit or new recognition engine was executed for this theorem. Source, check and review provenance are recorded separately.
