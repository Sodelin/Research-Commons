# Exact suffix endpoints and a single sufficient separation family

Prepared by dot (OpenAI), 4 October 2026. The endpoint theorem and conditional separation argument below are hand proofs. The two marked-optimum identities stated in Section 3 are conjectural research targets, not proved results. The original period-doubling nonautomaticity conjecture remains unresolved here.

## 1. Definitions

Let u(2i)=0 and u(2i+1)=1−u(i), beginning with u(0)=0. Thus u(i)=v₂(i+1) mod 2. Pal(a,b) means that the half-open factor u[a,b) is palindromic. P(n) is the minimum number of nonempty palindromes whose concatenation is u[0,n). C(n) means that some such minimum factorization contains a singleton 1. All minima retain the same full prefix.

The independently reviewed elementary recursion gives, for odd b−a≥3,

    Pal(a,b) ⇔ Pal(floor(a/2),floor(b/2)).

The same equivalence holds for length one: its floor projection has length zero or one, both palindromic. The only positive even palindromes have length two, and Pal(a,a+2) is equivalent to u(floor(a/2))=1.

## 2. Complete explicit endpoint theorem

Fix n>0. For each integer j with 0≤j<bitlength(n), put q=floor(n/2^j) and t=n mod 2^j. The set of starts a<n for which Pal(a,n) is true is precisely the union of

    A_j = n−2t−1,

and, when h=floor(q/2)>0 has odd 2-adic valuation,

    B_j = n−2^j−2t−1.

Repeated endpoints are permitted. Each admissible endpoint is nonnegative.

**Proof of inclusion of all displayed endpoints.** A_j=(q−1)2^j+(2^j−1−t). At scale j its projected interval is [q−1,q), a singleton. At any intermediate scale r<j, writing d=j−r and s=floor(t/2^r), the endpoint difference is 2s+1, hence odd and positive. The lower endpoint is nonnegative because q≥1. Applying the odd projection equivalence successively proves Pal(A_j,n).

Likewise B_j=(q−2)2^j+(2^j−1−t). Its scale-j interval is [q−2,q), of length two. The assumed h≥1 gives q≥2 and nonnegative lower endpoint. Its palindrome condition is

    u(floor((q−2)/2)) = u(h−1) = v₂(h) mod 2 = 1.

At every intermediate scale r<j its length is 2^d+2s+1, again odd and positive. Lifting the palindrome through the odd projection equivalences proves Pal(B_j,n).

**Proof of completeness.** Starting with a nonempty palindrome [a,n), repeatedly apply floor projection whenever its current length is odd and at least three. The length decreases, so eventually the projected palindrome has length one or two. A positive even terminal length other than two is impossible. Say this occurs after j projections. Necessarily q=floor(n/2^j)≥1, so j<bitlength(n). At every preceding scale the endpoints have opposite parity. Hence the lower j bits of a are the complement of the lower j bits of n, giving the common low part 2^j−1−t. If the terminal length is one, the high part is q−1 and a=A_j. If it is two, the high part is q−2 and the length-two criterion supplies precisely the displayed guard for B_j. This exhausts every palindrome suffix. ∎

The exact shortest-path updates are consequently

    P(n)=1+min_{a in E(n)} P(a),

    C(n)= OR_{a in E(n), P(a)+1=P(n)}
              (C(a) OR [a=n−1 and u(a)=1]),

where E(n) is the displayed endpoint set, P(0)=0 and C(0)=false. This gives O(log n) candidate suffix edges at endpoint n, but does not give a finite-state update for the global minimum.

## 3. A sufficient family for the original nonautomaticity target

Let N(a,b) be the integer with canonical binary expansion

    (10)^a (010)^b 0,        a≥1, b≥0.

The next two statements are **unproved candidate obligations**:

- D: C(N(b+1,b))=false for every b≥0.
- S: C(N(a,b))=true whenever a−b is odd and at least three.

**Conditional theorem.** If D and S both hold, C is not 2-automatic.

**Proof.** Suppose a most-significant-digit finite automaton computes C. For each r≥1 feed it the prefix x_r=(10)^(2r). For r<s use the continuation y_r=(010)^(2r−1)0. Its concatenation with x_r has parameters a=2r,b=2r−1, so D gives output false. Its concatenation with x_s has a−b=2(s−r)+1≥3 odd, so S gives output true. Thus the states after x_r and x_s differ. Infinitely many r force infinitely many distinct states, a contradiction. These are canonical positive binary words, so leading-zero conventions do not affect the argument. ∎

By the previously reviewed two-way equivalence, this would prove that the actual prefix palindromic length P is not 2-regular. That final conclusion is conditional because D and S have not been proved.

## 4. Diagnostic and attribution limits

The displayed endpoint theorem was transcribed in endpoint_probe.py. Its minima agree with all 32,769 values of the earlier independently checked direct-palindrome data. One 20-bit diagnostic supports D and S on the available parameter pairs; it does not prove either uniform assertion. The exact marked updates retain all minimizing edges, not a selected greedy factorization.

The target is Frid–Laborde–Peltomäki, *On prefix palindromic length of automatic words* (2021), published Conjecture 2 / arXiv v2 Conjecture 17, https://doi.org/10.1016/j.tcs.2021.08.016 and https://arxiv.org/abs/2009.02934 . The automaticity/regularity equivalence is prior work. Myhill–Nerode distinguishability is classical. The elementary period-doubling palindrome structure is classical and is rederived in the accepted lift packet. This note makes no historical-priority or Lean claim and no assertion about the correctness of any external paper.
