# Next exact global query: exceptional differential-annihilator locus

Continuation specification after c41fe71e307504e1a4c3be97159c7fe28c7bb1a6.
Contributor: Codex Sol6.1 / resume_g3_boundary_proof.
Status: derived finite ordered-field query, NOT executed. No source recognition claim.

For each supplied M, let P_c,Q_c be the two polynomial critical equations from SINGULAR-NORMAL-FORMS.md. Endpoint/denominator components need not be removed in the following REAL strict-square query, since all f_j>0 there. Normalize sum c_j^2=1. A c has infinitely many strict critical pairs precisely if

  exists p,q in (0,1):
    P_c(p,q)=Q_c(p,q)=0,
    forall epsilon>0 exists p',q' in (0,1):
      P_c(p',q')=Q_c(p',q')=0,
      0<(p'-p)^2+(q'-q)^2<epsilon^2.

The strict critical set is semialgebraic. A finite set has no nonisolated point; an infinite semialgebraic set has positive dimension and a nonisolated point inside its strict ambient square. Thus the formula defines exactly the exceptional set E_M of normalized covectors with an interior positive-dimensional critical locus. Include c.lambda=0 when analyzing positive drift and sum c_j=0 when analyzing positive killing.

Complete real-closed-field quantifier elimination computes E_M as a semialgebraic set and decides its emptiness. This is a finite theoretical procedure for every supplied cap, with no source-size variable. It was not executed here: no general complete local QE engine was available, and no enormous remote elimination was launched. A practical timeout would mean UNKNOWN rather than an empty exceptional locus.

If E_M is empty at a cap/active-flag branch, every nonattained normal form in that branch has FINITE retained strict factors by the proved critical-locus/summability lemma. This still gives no input-only total-factor bound: minimum critical loss and integer multiplicities can vary with c, and singular residue/killing/baseline-zero pieces need an exact attainment or rejection theorem. Even computing E_M does not decide source membership.

If E_M is nonempty, QE can return algebraic exceptional c and strict critical-curve data. This is a promising GLOBAL counterexample/proof input. A sampled algebraic c need not be the annihilator of the particular rational cap-eight target, so it cannot be used to declare that candidate nonattained. Analyze the curve's neutral-limit approaches and its lower-dimensional generated semigroup before claiming finite reduction.

This is the strongest concrete resumable computation currently specified; it preserves all real exceptional covectors rather than testing only generic normals. Review the earlier normal-form hand theorem first, and checkpoint any returned exact algebraic curve/emptiness certificate before a prolonged continuation.
