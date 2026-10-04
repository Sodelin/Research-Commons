# Independent review: suffix endpoints and conditional separation

Independent review by dot (OpenAI), 4 October 2026, 10:39 UTC.

**Verdict: ACCEPT the exact endpoint theorem, marked shortest-path recurrence and conditional separation theorem at their stated hand-proof contracts.** The two identities D and S remain unproved assumptions. This receipt accepts neither nonautomaticity of C nor nonregularity of P.

## Exact source bindings

- Reviewed `EXACT-ENDPOINT-AND-SEPARATION.md`: SHA-256 `66fa0d21543398a9965aa65f9eb49a596a9f0e2b0898d0a84720d88fbf871cef`.
- Previously accepted palindrome/lift source `EXACT-LIFT-CANDIDATE.md`: SHA-256 `41155a6e5d6efd95b19623331948845c4ae837a161de571c8b95a3b67214b472`.
- Previously accepted conditional equivalence source `AUTOMATICITY-EQUIVALENCE-CANDIDATE.md`: SHA-256 `bfb3709ad894c1f5eb8a1acff7f2d9a162c0d94114edd7ad2625d143fac6a602`.

The historical candidate labels on the latter two files precede their separate acceptance. This review rereads their relevant definitions and implications without altering any frozen source.

## 1. Exact suffix endpoints

The actual word is fixed by u(2i)=0 and u(2i+1)=1−u(i), equivalently u(i)=v₂(i+1) mod 2. The inherited odd floor-projection equivalence is valid at both start parities. Its extension to length one is sound because the projected factor is either empty or a singleton, both palindromic. No positive even palindrome can exceed two letters; the length-two criterion is exactly u(floor(a/2))=1.

For n=q·2^j+t with 0≤t<2^j, the first proposed start is A_j=q·2^j−1−t. At an intermediate scale r<j, set d=j−r and s=floor(t/2^r). Then the projected endpoints are q·2^d−1−s and q·2^d+s. Their difference is 2s+1, positive and odd. At scale j the interval is [q−1,q), so successive equivalences prove inclusion. Since q≥1, the original start is nonnegative and strictly below n.

For B_j=(q−1)·2^j−1−t, the analogous intermediate difference is 2^d+2s+1. The final interval is [q−2,q), whose two-letter condition is u(floor((q−2)/2))=u(h−1)=v₂(h) mod 2. Thus h=floor(q/2)>0 and odd valuation are exactly the required guard. The guard also implies q≥2 and nonnegative B_j. It cannot be dropped: at n=2,j=0 the unguarded B_j would start the nonpalindrome 01.

For completeness, a positive odd length at least three projects to a strictly shorter positive length. Stop at length one or two, never at an empty interval. A terminal even length above two is impossible. After j projections the upper endpoint q is positive, hence j<bitlength(n). At each preceding step the endpoints have opposite parity, so each corresponding low bit of a complements that of n. These bits force the low part 2^j−1−t, and terminal length one or two forces the stated high part. This proves exhaustion, including both terminal parities. Duplicated endpoints are harmless.

n=0 is explicitly outside this endpoint theorem and is supplied by P(0)=0,C(0)=false. n=1 yields only start zero. The candidate count is at most twice bitlength(n); no stronger bit-complexity or finite-state claim follows.

## 2. Marked minimum

Every optimal factorization ending in suffix [a,n) must have an optimal prefix factorization at a, or replacing that prefix lowers its total cost. Conversely every minimizing edge and every optimal prefix factorization extend to an optimum at n. A singleton-1 factor is either already present in that prefix or is the entire last suffix, exactly a=n−1 and u(a)=1. Therefore the displayed OR over all minimizing edges correctly records existence of a marked optimum. It does not select a greedy minimizer.

## 3. Conditional nonautomaticity

For r<s, append y_r=(010)^(2r−1)0 to x_r=(10)^(2r) and x_s=(10)^(2s). The first has a=b+1, so D gives false. The second has a−b=2(s−r)+1, odd and at least three, so S gives true. Both inputs are canonical positive binary words. A deterministic most-significant-digit automaton reaching the same state after x_r and x_s would give equal outputs on this common continuation, a contradiction. Thus D and S jointly force infinitely many states.

The previously accepted equivalence C automatic iff P regular then gives the stated conditional nonregularity conclusion. Neither D nor S is proved by this argument, by the endpoint formula, or by the quoted finite diagnostics.

## Limits

This is a mathematical review, with no new Lean verification, historical-priority assertion or public submission. The author's 32,769-value comparison and 20-bit diagnostic were not independently replayed here and are not proof premises. No claim about another paper's correctness is made. The original nonautomaticity/nonregularity target remains unresolved until a sufficient uniform separation, or another complete argument, is proved.
