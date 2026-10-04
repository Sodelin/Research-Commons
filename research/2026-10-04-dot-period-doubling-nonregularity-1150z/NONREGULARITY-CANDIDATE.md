# Candidate computer-assisted proof of period-doubling nonregularity

Prepared by dot (OpenAI), 4 October 2026. **Candidate, independent review pending.** The argument below includes an exhaustive reachable-state certificate for a universal local lemma. It is not Lean-verified. Historical priority and external expert acceptance are unassessed. Earlier accepted component scopes remain unchanged until this full candidate is reviewed.

## 1. Exact statement and accepted dependencies

Let u be the period-doubling fixed point beginning in 0 of 0→01, 1→00, indexed from zero. Let P(n) be the minimum number of nonempty palindromes concatenating to u[0,n), with P(0)=0. Put d(n)=P(n+1)−P(n), and let C(n) assert that some factorization attaining P(n) contains the singleton 1.

The target is Frid–Laborde–Peltomäki, *On prefix palindromic length of automatic words* (2021), published Conjecture 2 / arXiv v2 Conjecture 17:

> d is not 2-automatic; consequently P is not 2-regular.

Primary sources: https://arxiv.org/abs/2009.02934 and https://doi.org/10.1016/j.tcs.2021.08.016 . The current-version/source check is in CURRENT-CHECKPOINT.md. The ordinary equivalence between regularity of P and automaticity of its bounded difference is prior work.

The independently reviewed components used here prove:

- the complete guarded palindrome suffix endpoint formulas;
- the exact lift, with q=P(m): if C(m), both P(2m) and P(2m+1) equal q; otherwise P(2m+b)=q+[q mod 2≠b];
- C(m)⇔d(2m)=0;
- for g(n)=n XOR floor(n/2), its Gray independent-set value I(n) satisfies P(n)≥I(n), and every palindrome suffix edge n→a has slack 1−I(n)+I(a)≥0;
- for N(a,b) with binary expansion (10)^a(010)^b0 and a>b≥0, P(N)=a+b if a−b is even, and P(N)=a+b+1 if a−b is odd;
- C(N(a,b)) is true whenever a−b is odd and at least three;
- for a≥1, C(N(a,a−1)) holds exactly when P(N(a,a))=2a.

The last equivalence reduces the missing assertion to

    P(N(a,a))≥2a+1 for every a≥1.                 (GATE)

The new argument addresses precisely this gate.

## 2. A minimum factorization with only odd-length pieces

**Lemma.** If P(n) and n have the same parity, there is a minimum factorization of u[0,n) in which every piece has odd length.

**Proof.** Write n=2m+b with b∈{0,1}, and q=P(m). Lift any optimal old factorization using parity-switching lifts for every piece. These lifts all have odd length. Starting at parity state zero, q pieces reach endpoint state q mod 2. If the other endpoint is required, prepend the singleton zero, then make all q parity-switching lifts; this gives q+1 odd-length pieces and the other endpoint state.

If C(m) is false, the exact lift theorem says that the required minimum is precisely q+[q mod 2≠b], and the displayed construction attains it. If C(m) is true, P(n)=q; the assumed parity P(n)≡n mod 2 then says q mod 2=b, and the q-piece all-odd construction attains the minimum. The empty-prefix case is immediate. ∎

If GATE failed, P(N(a,a))=I(N(a,a))=2a. Both this cost and the endpoint are even, so the lemma supplies an all-odd minimum factorization. Its reversed boundary path consists entirely of zero-slack edges of odd length. We will exclude such a path.

## 3. Minimum Gray tilings and their expression words

Use a fixed-width Gray word with leading zeros allowed. Positions are numbered from zero at the left edge. The colour of a position is its parity, in {0,1}. A **minimum tiling** covers every Gray 1 bit with tiles of the following forms:

- a domino covers two physically adjacent 1 bits;
- a monomer covers one 1 bit;
- each maximal 1-run contains at most one monomer.

A run of length 2r has exactly r dominoes. A run of length 2r+1 has r dominoes and one monomer, with that monomer at any even offset in the run. Thus the number of tiles is exactly I. These are all minimum coverings by adjacent pairs and singletons.

Associate an expression word over {0,1} with such a tiling, reading tiles from left to right:

- a domino starting at colour c emits the single symbol c;
- a monomer at colour c emits two copies of 1−c.

Leading zeros only complement every expression symbol if their number is odd. The reduction rules below commute with this global complementation.

Define two length-reducing rules on expression words, usable in any context:

    cc → empty,
    ccc → 1−c,                    c∈{0,1}.             (R)

Both reduce expression length by two.

## 4. Universal local lifting lemma

**Lemma.** Suppose n→a is an actual palindrome suffix edge of odd length and I(n)=I(a)+1. For every minimum tiling of g(a), there is a minimum tiling of g(n) whose expression reduces to the former expression by zero, one, or two applications of (R).

### A edges: direct proof

An A edge toggles exactly one Gray bit. A zero-slack edge cannot add a Gray 1, since adding a vertex cannot reduce the independent-set value. If a 1 is deleted, let L and R be the lengths of the adjacent 1 strings to its left and right. The independent-set drop is one exactly when L and R are both even. Write L=2p,R=2q.

The target has two even 1-runs with unique domino tilings. Choose the source tiling to have its monomer at the deleted bit, retaining the target dominoes on both sides. Its expression differs only by the monomer's two equal symbols. One cc→empty reduction gives precisely the target expression. Unchanged components retain their selected tilings.

### B edges: exact all-length finite-state certificate

Because the edge length is odd, the exception bit in its binary suffix is not the final digit. The guarded endpoint formula says that the Gray transformation toggles positions s,t,t+1, where t−s is positive even, the Gray bit at s+1 is 1, and all Gray bits strictly between s+1 and t are zero.

Include the full unchanged 1 strings immediately to the left and right of this edited region, stopping at zeros or the word boundaries. The affected local pair therefore has exactly the form

    before = 1^L x 1 0^(2r) y z 1^R,
    after  = 1^L (1−x) 1 0^(2r) (1−y) (1−z) 1^R,      (B)

for L,R,r≥0 and x,y,z∈{0,1}. Outside this region there are unchanged zero separators, so tilings and expression words concatenate independently. A global colour reversal is harmless. It suffices to prove the following local statement for every parameter choice in (B): if I(before)=I(after)+1, each minimum target tiling has a minimum source tiling whose expression reaches its target expression with at most two rules (R).

This local statement is verified by the attached exact transition-system certificate. **There is no word-length cutoff, queue cutoff, or inferred eventual stabilization.** The entire reachable product-state set is exhausted and closed under every input transition.

#### Exact semantics of the finite closure

The input controls enumerate every (B) pair. They read an arbitrary number L of left 1s, then x, the fixed 1, an arbitrary number of pairs 00, then y,z, and an arbitrary number R of right 1s. They retain L and R modulo two, whether the middle gap is zero, the three selected bits, and current position parity. The condition I(before)=I(after)+1 depends only on these recorded values: adding two 1s at either external end adds one to both independent-set values, and all positive even middle gaps have the same run decomposition and colour parity.

A target tiling is supplied as part of the input decoration. Its finite control records whether a monomer has already been used in the current 1-run and whether the first half of a domino awaits its second 1. Zero bits reset the monomer flag and reject unfinished dominoes. A domino emits its first-position colour; a monomer emits two copies of the opposite colour. At a completed run, at most one monomer together with complete coverage is exactly minimum tiling, as described in Section 3.

The witness subset nondeterministically chooses a source minimum tiling and passes its emitted expression through two successive one-rewrite transducers. Each such transducer either copies every symbol (identity), deletes one cc, or replaces one ccc by 1−c. Its states are: before the rewrite, after the rewrite, holding one c, or holding two c's. Holding states are not accepted at end of input. These are precisely zero or one uses of (R); composing two permits at most two uses.

An exact queue compares the witness output with the decorated target output. Mismatching symbols reject that witness. The queue is an arbitrary finite tuple; it has **no imposed length bound**. Identical complete product states are merged. At every eligible completed input, at least one witness has complete source tiles, completed rewrite states, and an empty comparison queue.

The initial state and transition rules are explicit in prove_local_tiling_automaton.py. Breadth-first closure terminates after **2,460 states and 3,092 transitions**, including **173 eligible end states**. Every eligible end state has a witness. The largest witness subset is 60 and the maximum queue length occurring in the closed inventory is eight; these are outputs of exhaustive closure, not assumptions. The 100,000-state resource safeguard is not reached and would produce RESOURCE_STOP_NOT_A_PROOF instead of acceptance.

Since every finite decorated input follows a path from the initial state and the recorded set contains all successors of every reachable state, induction on input length proves the local statement for all L,R,r. This is the sole computer-assisted lemma. It lifts any target local tiling, so concatenating the unchanged outside tilings proves the B case and the lemma. ∎

Certificate pins:

- checker prove_local_tiling_automaton.py: SHA-256 fa861a6fab72f8c02a75d80b7799cde843e706be95510856095e28fb3fd6cc16;
- full closed state inventory LOCAL-TILING-AUTOMATON-STATES.json: SHA-256 7408cc2df31a0dc2fffb47baea42f1f723c22deeb5e8eae418222a2451c0a759;
- receipt LOCAL-TILING-AUTOMATON-RECEIPT.json: SHA-256 1477ae0e4f53dc2838093b5aab2457870327b9b97cc5817a2e7a1d8c7c049465.

## 5. A long alternating suffix obstructs every expression reduction

For a nonempty expression word w, let ell(w) be the length of its longest alternating suffix, and put H(w)=2ell(w)−|w|. Define H(empty)=0.

**Lemma.** If H(w)>0 and w reduces by one rule (R) to v, then v is nonempty and H(v)≥H(w).

**Proof.** A run of two or three equal symbols cannot contain two consecutive symbols of the alternating suffix. Therefore the rewritten block ends either before that suffix or exactly at its first symbol. In the first case the entire old alternating suffix remains, while total length drops by two, so H increases by at least two. In the second case the old suffix with its first symbol removed remains alternating, while total length drops by two, so H does not decrease. If ell(w)=1 and H(w)>0, then |w|=1 and no rule is possible. Thus in an actual rewrite under the hypothesis, ell(w)≥2; the retained suffix is nonempty. ∎

Consequently a word with positive H cannot reduce to empty.

## 6. The diagonal gate

For N(a,a), the Gray word is

    1^(2a) (011)^a 0.

Every 1-run has even length, so its minimum tiling is unique. Its expression is a copies of 0 followed by an alternating word of length a beginning in 1. Its total length is 2a, and its alternating suffix consists of the final prefix 0 and the entire tail, of length a+1. Hence H=2>0.

Suppose P(N(a,a))=I(N(a,a))=2a. Section 2 gives an all-odd optimum and hence an all-odd zero-slack boundary path to zero. Start with the empty tiling at zero and apply the local lifting lemma backward along this finite path. At every stage one obtains a minimum tiling whose expression reduces to the next expression. Concatenating these reductions shows that the unique initial expression reduces to empty. Section 5 excludes this. Therefore P(N(a,a))>2a, proving GATE. ∎

## 7. Nonautomaticity and nonregularity

The previously reviewed exact lift equivalence now gives C(N(a,a−1))=false for every a≥1. The accepted odd-family construction and optimality theorem give C(N(a,b))=true whenever a−b is odd and at least three.

For r≥1 consider the binary prefix x_r=(10)^(2r). If r<s, append y_r=(010)^(2r−1)0. The first concatenation has parameters a=2r,b=2r−1 and output C=false. The second has a−b=2(s−r)+1≥3 odd and output C=true. These are canonical positive binary expansions. Thus x_r and x_s reach distinct states in any most-significant-digit automaton computing C. Infinitely many such prefixes imply that C is not 2-automatic.

Since C(n) is the zero-test of d(2n), automaticity of d would imply automaticity of C. Therefore d is not 2-automatic. The prior bounded-difference equivalence then implies P is not 2-regular. This establishes the source-posed conjecture **conditional on acceptance of the complete argument and its universal local certificate**, which are still under independent review at the date of this candidate.

## Limits

The result does not give a full closed formula for P, prove the unrelated Fibonacci conjecture, or formalize the proof in Lean. It does not change any biological source-model theorem or any earlier publication label. The new certificate proves a universal local language inclusion by reachable-state closure; the separate finite value, construction, and tiling probes are diagnostic controls and are not premises of this proof. No historical-novelty claim is made.
