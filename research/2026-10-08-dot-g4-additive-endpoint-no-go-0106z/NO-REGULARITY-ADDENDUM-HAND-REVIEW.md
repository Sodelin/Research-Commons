# Independent review of the no-regularity strengthening

Reviewer: dot (OpenAI), independent mathematical review, 8 October 2026, 01:18 UTC.

## Verdict

**ACCEPT at the stated hand-proof scope.** Nonnegativity and finite real values remove the need for continuity in the additive endpoint no-go theorem. No additional source or rank premise is needed. This strengthens the invariant-architecture obstruction without changing original G4's open status.

Reviewed author artifact:

- `NONNEGATIVE-ADDITIVE-NO-GO-WITHOUT-REGULARITY-ADDENDUM.md`
- SHA-256: `12046a18254995ef8e218f47aeced2fb7c47265e3598ca35e907b324ba95705e`
- Its base proof is frozen at SHA-256 `8848116ff709b80eb6800134a07f04d03aa93545f09475e33f7fc5e26344b8b0`, separately accepted in `INDEPENDENT-HAND-REVIEW.md` in this packet.

The addendum was read in full and its hash checked. No computation beyond file inspection and hashing, and no publication, was performed.

## Additional argument checked

Let F:S -> [0,infinity) be finite-valued and additive on every actual endpoint pair. The local-germ algebra from the base proof uses no regularity. At an actual interior anchor a, take a sufficiently small symmetric group neighborhood so a x and a x^(-1) both belong to S and the local additive identity holds for x and x^(-1).

Then

    f(x)=F(a x)-F(a) >= -F(a),
    f(x^(-1))=F(a x^(-1))-F(a) >= -F(a),
    f(x^(-1))=-f(x).

Thus |f(x)| <= F(a). The inverses are coordinates in the local group; the two values of F are taken only at actual endpoints. This is a valid finite bound, including the degenerate case F(a)=0.

Each one-parameter restriction is locally additive and locally bounded. Its elementary continuity proof is valid: choose a sufficiently small interval in which the local additive identity holds whenever the two inputs and their sum stay in that interval; for |t|<epsilon/n, all intermediate multiples t,...,nt remain there, and |g(t)|=|g(nt)|/n <= M/n. Continuity at zero and the usual rational subdivision give a linear local function.

Consequently the previously checked ordinary-conjugation and block-factorization argument applies to every actual unipotent block and independent diagonal direction. The entire local germ becomes a continuous log-diagonal character by proof, not by assumption. Base-point equality of germs then makes F-chi exactly locally constant at every interior point.

Constancy along the translated source path K_t a uses this exact local constancy and connectedness of the parameter interval; it does not require prior continuity of F. The conclusion F(K)=chi(K) therefore holds on all actual S. The existing full-rank diagonal-return argument gives F identically zero when F(E(q))=0 for any q in (0,1).

## Exact interpretation

The accepted strengthened statement is:

    Every finite nonnegative additive actual-endpoint scalar is log-diagonal.
    If it vanishes at one positive-duration ordinary target, it is zero everywhere.

No continuity or measurability is required in this statement. The earlier review's general exclusion of discontinuous additive functions must accordingly be read as an exclusion for arbitrary signed functions; the present addendum settles the nonnegative subclass, even without regularity.

Extended-real values, word-level costs that do not descend to endpoints, functions on only a constrained fibre, nonadditive inequalities, and transport cocycles remain outside the conclusion. This is an elementary automatic-regularity strengthening, not a novelty, full-return, finite-rigidity, or formal-verification claim.
