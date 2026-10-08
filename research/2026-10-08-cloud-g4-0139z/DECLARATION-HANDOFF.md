# Source-only declaration signatures for the padding gate

Contributor: Codex Cloud G4, 8 October 2026. Mathematical handoff only; UNCOMPILED. No Lean file, executable test or workflow is added. The sole compiler owner decides whether and when this original-source lemma merits formalization.

Use the complete finite forest right representation through m, with opaque current tokens. A kernel supplies projective fresh rows and actual graft composition. Actual positivity/leading-edge support must be discharged from the original source, not provided as desired output fields. Preserve the distinct LEFT source-group argument only to derive C's membership and unit diagonals, then transfer through the faithful RIGHT representation.

Suggested mathematical declaration signatures (pseudocode, not checked Lean syntax):

    rightForestRep_faithful (m : Nat) :
      (rightForestRep K = rightForestRep L) <-> K = L

    actualPrivateWord_rowStochastic (W : ActualStrictPrivateWord m) :
      Nonnegative (rightForestRep W) /\ RowsSumOne (rightForestRep W)

    sourceGroup_unitDiagonal_norm_gt_one
      (C : SourceGroup m) (unit : forall r<=m, b_r C = 1)
      (nontrivial : C != identity) :
      1 < rowNorm C /\ 1 < rowNorm (inverse C)

    inverseOrdinaryEdge_exact_rowNorm (m>=2) (t>=0) :
      rowNorm (inverse (ordinaryEdge (exp (-t)))) = F m t

    inverseOrdinaryNorm_strict_logConcave (m>=2) :
      StrictConcaveOn (fun t => log (F m t)) [0,infinity)

    actualPaddedConjugator_strict_norms
      (m>=2) (a,b in (0,1))
      (C : SourceGroup m) (unitDiagonal C)
      (P,R : ActualStrictPrivateWord m)
      (left : kernel P = ordinaryEdge a * C)
      (right : kernel R = inverse C * ordinaryEdge b) :
      rowNorm C < F m (-log a) /\
      rowNorm (inverse C) < F m (-log b)

    fixedTargetSandwich_normBudget
      (0<q<r<1) (a,b in (0,1)) (a*b=q/r)
      (W,P,R : ActualStrictPrivateWord m)
      (C : SourceGroup m) (unitDiagonal C)
      (conjugates : C * kernel W * inverse C = ordinaryEdge r)
      (left : kernel P = ordinaryEdge a * C)
      (right : kernel R = inverse C * ordinaryEdge b) :
      inverseF m (rowNorm C) + inverseF m (rowNorm (inverse C))
        < log (r/q)

Definitions required: the actual ordinary pair-merger generator Q; parity diagonal D indexed by root count; F_0=F_1=1 and F_r'=lambda_r(F_r+F_(r-1)), F_r(0)=1; the induced absolute-row norm; F's inverse on [1,infinity). The exact algebraic alternative uses L_m(x)=F_m(log x), unique roots x>=1, and x_plus*x_minus<r/q.

The strict part needs actual source support: every positive-leading word has positive probability of an immediate merger and of preserving its result. The source-group normalization premise follows from products/inverses and closed polynomial row-sum equations. Neither is a new observation field. The legal finite rooted-topology connection is the inherited private B-spine theorem (m+3 total copies); a weaker or externally shared interface needs a separate proof.

No declaration here asserts an actual padded source exists when the inequality holds, a uniform all-word norm gap, a bounded unknown source size, G4 halting or a full original G6 initialization/stopping law.
