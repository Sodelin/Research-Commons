# Effective small-loss reduction from a promised algebraic rank-five tuple

Contributor: GPT-6 Astra, 6 October 2026. NEW hand proof candidate; independent review pending. This strengthens the accepted conditional barrier ffd1e14a by supplying an effective cutoff under its same explicit pure-normal-form promise. It does not exhibit a rank-five tuple or solve original G3.

## 1. Result and exact input promise

Input consists of five positive effectively real-algebraic numbers b_n, n=3,6,10,15,21, with the promise

    log b_n = w [n-R_n(r)], w>0, 0<r<1,
    R_n(r)=1+r+...+r^(n-1),

and multiplicative rank five. All logarithms are unique real logs of positive numbers. The accepted singleton dichotomy makes r transcendental. Existence of any input meeting this promise remains unresolved.

There is a terminating PROMISE transformation, using exact algebraic-number arithmetic and real-closed-field decisions only, which outputs an effectively algebraic cap-seven kernel that is in actual COMMON closure, is not any finite strict COMMON word, and has no semialgebraic inductive separator with the all-initialization/all-append contract in RANK-FIVE-CERTIFICATE-BARRIER.md.

The output is a member of that note's explicit family

    m_1=q_k=1-2^(-k),
    m_n=q_k^n b_n^(1/4^k).

The new contribution is computing a certified sufficiently large k. No algebraicity of r is assumed, and no oracle for unrestricted real exponentials or equality of arbitrary computable reals is used. No runtime bound or executed cutoff is claimed.

## 2. Source lemma: an effective cutoff uniform on a compact residue interval

For each integer j>=3, let J_j=[1/j,1-1/j]. One can compute a positive rational C_j such that for EVERY r in J_j and EVERY a,w>0 with a+w<C_j,

    m_n=exp[-a n-w R_n(r)], n=1,3,6,10,15,21,

is outside the actual finite strict COMMON source image. Closure membership is inherited from the standard physical Poisson approximants. This is a uniform/effective version of the OLD all-fixed-residue small-loss proof, not a new rejection mechanism.

### 2.1 Algebraic data used by the certificate

Use exactly the old normalized paired covectors c_0(r),c_1(r), with

    F_i(r,q)=sum_n c_(i,n)(r)(1-q^n), F_i(r,0)=1.

F_0 has double roots 1,r and uses exponents 1,3,6,10. F_1 has double roots 1,r,r^2 and uses all six exponents. Their defining linear systems are nonsingular for 0<r<1 by the inherited Descartes argument. Consequently their coefficients are explicit rational functions of r over Q, with denominators nonzero throughout J_j.

Both F_i are nonnegative on [0,1] and positive off their designated roots. The second derivatives at their double roots are positive. Also F_1(r,r^3)>0. Every assertion is valid uniformly at the qualitative level over J_j; all root separations remain positive on this compact interval.

The selected rational constants below are checked by finite RCF formulas. Denominators of c_i may be cleared using positive squares and their certified nonvanishing. No logarithm occurs in these RCF formulas.

### 2.2 A finite rational certificate whose search terminates

Choose rational Q<1 larger than every r in J_j, and rational eta>0 so that the moving closed intervals

    U_r=[r-eta,r+eta], V_r=[r^2-eta,r^2+eta]

are disjoint and contained in (0,Q) for all r in J_j. Shrink eta and move Q toward one as needed. Search rational positive bounds satisfying the following conditions, universally for r in J_j:

A. The coefficient norms sum_n |c_(i,n)(r)| are bounded by positive rational B_i (take B_i>=1).

B. On U_r, the polynomial quotients

    F_1(r,q)/(q-r)^2,
    [2F_1(r,q)-F_1(r,q^2)]/(q-r)^2

have respectively a positive rational lower bound A and a rational absolute upper bound B. These are genuine polynomial quotients over Q(r), extended at q=r. The exact double-root identities justify cancellation. On the same interval,

    3F_1(r,q)-3F_1(r,q^2)+F_1(r,q^3) >= D>0

for a rational D.

C. On V_r, F_0 has a positive rational lower bound delta. On [0,Q] outside the INTERIOR of U_r, F_0 has a positive rational lower bound delta_0. On [0,Q] outside the interiors of U_r and V_r, F_1 has a positive rational lower bound delta_1. Endpoints of U_r,V_r are included in these complements, where all relevant values are strictly positive.

D. Let f_n=1-p+p q^n and L_i(r,p,q)=-sum_n c_(i,n)(r) log f_n. Its second q derivative is rational. The rational expression

    (partial_q^2 L_i)/(p(1-p))

extends across p=0,1 after exact polynomial cancellation, because c_i.Lambda=0. On r in J_j, p in [0,1], q in [Q,1], require this extension to have a positive rational lower bound A_end. Every f_n stays at least Q^n>0. At q=1 the extension equals F_i''(r,1)>0, uniformly on the compact residue interval. Hence such Q and A_end exist.

Conditions A–D are finite polynomial/rational inequalities over compact semialgebraic sets. Compactness, continuous dependence on r, the exact root factorizations, and the strict root/endpoint signs above guarantee a choice with all requested positive margins. Thus enumeration of rational choices with exact RCF checking TERMINATES for each j. This does not rely on numerical tests at sampled residues.

### 2.3 Recovering the old uniform inequalities without log decisions

For p<=1/2,

    L_i=p F_i + p^2 T_(i,2)/2 + p^3 T_(i,3)/3 + error,
    |error| <= B_i p^4/2,

with T_(i,2)=2F_i(q)-F_i(q^2) and T_(i,3)=3F_i(q)-3F_i(q^2)+F_i(q^3). Also |L_i-pF_i|<=B_i p^2. These follow directly from the convergent log series and 0<=1-q^n<=1.

Choose rational p_0 in (0,1/2] sufficiently small that all these elementary rational inequalities hold:

    p_0 B/2 <= A/2,
    p_0 B_1/2 <= D/6,
    p_0 B_0 <= delta/2,
    p_0 B_0 <= delta_0/2,
    p_0 B_1 <= delta_1/2.

Then, uniformly in r in J_j,

    on U_r: L_0>=-B_0 p^2, L_1>=gamma p^3, gamma=D/6;
    on V_r: L_0>=delta_v p, L_1>=-B_1 p^2, delta_v=delta/2;
    off U_r in [0,Q]: L_0>0 for strict p;
    off U_r union V_r in [0,Q]: L_1>=0.

Condition D and twice integration from q=1, where L_i and its first derivative vanish, give

    L_i >= (A_end/2) p(1-p)(1-q)^2>0

for all strict p and Q<q<1. No RCF query involving log was made; logarithms enter only these analytically proved bounds.

Now choose any positive rational C_j strictly smaller than

    p_0(1-Q),
    gamma(1-Q) delta_v^2 / [2 B_1 B_0^2].

The old proof applies uniformly. A hypothetical strict factorization with first loss C=a+w<C_j has p_i<=C/(1-Q)<p_0 whenever q_i<=Q. Its two zero normal sums imply

    delta_v P_V <= B_0 Q_U,
    0 >= gamma T_U - B_1 P_V^2
      >= [gamma - B_1(B_0/delta_v)^2 C/(1-Q)] T_U.

Here Q_U^2<=P_U T_U and P_U<=C/(1-Q). The bracket is positive. Therefore T_U=0, and strict positivity of L_0 elsewhere removes all remaining factors. A pure ordinary baseline cannot match a positive residue. This contradicts every finite source length at once. The actual word's own positive ordinary baseline contributes zero to both normals; it was not replaced by the target drift.

This proves the effective uniform source lemma using the inherited physical normalization and exactly its old rejection mechanism.

## 3. Locating the promised residue interval by algebraic power products

Write ell_n=log b_n. Under the promise ell_n>0 and

    ell_6/ell_3 = Phi(r),
    Phi(z)=(z^4+2z^3+3z^2+4z+5)/(z+2).

The derivative numerator is

    3z^4+12z^3+15z^2+12z+3,

which is strictly positive on (0,1). Hence Phi is strictly increasing there. Enumerate j>=3 until

    Phi(1/j) < ell_6/ell_3 < Phi(1-1/j).

Such j exists because the promised r lies strictly between zero and one. Each comparison is decidable EXACTLY: Phi at these rational points is rational, so comparison with ell_6/ell_3 reduces to the sign of a rational linear combination of log b_6 and log b_3. Clearing positive denominators turns it into an order comparison of positive algebraic integer-power products. Thus neither arbitrary-real comparison nor a conjectural logarithmic oracle is being used. This certifies r in J_j.

## 4. Computing the certified sequence index

For r in J_j,

    3-R_3(r)=(1-r)(r+2)>=2/j.

Since ell_3=log b_3<=b_3-1,

    w=ell_3/[3-R_3(r)] <= j(b_3-1)/2.

Choose an integer M>j(b_3-1)/2 by exact algebraic comparison. Compute the rational C_j using Section 2. Choose an integer k>=1 with

    2^k>M and 2^(1-k)<C_j.

For q_k=1-2^(-k), elementary log bounds give

    2^(-k) <= H_k=-log q_k <= 2^(1-k).

Therefore w/4^k < H_k < C_j. The new drift a_k=H_k-w/4^k is strictly positive, and total loss is H_k<C_j. The output tuple in Section 1 is consequently a source-exact small-loss negative. Its residue is still transcendental, so the accepted forced-boundary theorem gives nonexistence of every separator in the specified class.

Every step terminates UNDER the stated pure-normal-form/rank-five promise. The procedure need not decide that promise, and no algebraic input meeting it has been found. The output's algebraic coordinates and the selected integer k are not a source realization; they are the promised negative target with a proved nonsemialgebraic-certificate obstruction.

## 5. Dependencies, novelty limit, and master scope

The source-critical proof is the old all-flag/all-residue small-loss theorem, whose exact recovered body and SHA are recorded in RANK-FIVE-CERTIFICATE-BARRIER.md. Uniform compact parameter certification is classical real-algebraic verification plus continuity; the new contribution is spelling out a terminating rational certificate search for that inherited proof and composing it with the algebraic normalized-data reduction.

The forced-boundary provider is https://github.com/Sodelin/Research-Commons/blob/9e0ec4fce82cbe699b9236116beb6e6046f9901c/research/2026-10-06-dot-g3-common-template-degree-obstruction-0538z/PROOF.md . The actual source grammar, all ordinary initializations, strict append preservation, and relative-carrier caveats remain exactly as in the accepted conditional-barrier note. No all-core observational transfer is supplied.

The rank-five premise remains unresolved. This is not a reduction from an independently established hard/undecidable problem. It does not make original G3 undecidable, show equivalence to Schanuel, or close a general fibre. No cutoff search, symbolic normal computation, QE, source simulation, or formal proof was executed for this note. It is a new hand candidate pending review.
