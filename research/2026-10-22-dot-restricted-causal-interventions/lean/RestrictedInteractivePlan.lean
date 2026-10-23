import FullClassQueryGame

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

An explicit uniform, response-branching G7 Plan with the original indexed
B query horizon. Marginals are asked first; their actual responses select
the conditioning masks for the two remaining families. Every branch is
legal and budgeted. Terminal correctness uses one source fitting the entire
executed history, with the exact original-source marked-TCM CLASS target.

The plan itself is computable from finite label/order/target data. Its
mathematical sourceGame target and the original unknown graphical response
specification are noncomputable; neither is evaluated in the plan body.
No extraction, runtime, sample-complexity or intervention-count claim.
-/

namespace RestrictedCausal.PartialQueries

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open HPLTarget ProfileRegistry FiniteTargetImage FiniteGraphDecision TranscriptDecoder
open ComputableCanonical QueryPlan GProgram.G7.ExactLawResourceGame

universe u v

def conditionalPlan {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (conditional : Enumeration (ConditionalIndex T))
    (m : X → X → Bool) (h : TranscriptDecoder.History X T) :
    Plan (ElementaryAction X T) Bool (Finset (TargetCode X T)) (0 + conditional.items.length) :=
  collect conditional.items (conditionalIndexAction T m)
    (fun _ fresh => Plan.stop (n := 0) (decodeHistory T fresh)) (fun _ => false) h

def observedPlan {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T))
    (m : X → X → Bool) (h : TranscriptDecoder.History X T) :
    Plan (ElementaryAction X T) Bool (Finset (TargetCode X T))
      ((0 + conditional.items.length) + observed.items.length) :=
  collect observed.items (observedIndexAction T m)
    (fun _ fresh => conditionalPlan T conditional m fresh) (fun _ => false) h

def restrictedPlanRaw {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T]
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T)) :
    Plan (ElementaryAction X T) Bool (Finset (TargetCode X T))
      (((0 + conditional.items.length) + observed.items.length) + marginals.items.length) :=
  collect marginals.items marginalIndexAction
    (fun replies fresh => observedPlan T observed conditional (maskFromReplies T replies) fresh)
    (fun _ => false) []

theorem recorded_of_rows {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (r : MarginalIndex T → Bool)
    (h : TranscriptDecoder.History X T)
    (rows : ∀ q : MarginalIndex T, (marginalIndexAction q, r q) ∈ h) :
    MarginalsRecorded (maskFromReplies T r) h := by
  intro target x distinct
  let q : MarginalIndex T := ⟨(target, x), distinct⟩
  change (marginalIndexAction q, !(maskFromReplies T r q.val.1.val q.val.2)) ∈ h
  rw [mask_from_replies_complement]
  exact rows q

theorem recorded_retained {X : Type u} {T : X → Prop}
    (m : X → X → Bool) (h fresh : TranscriptDecoder.History X T)
    (recorded : MarginalsRecorded m h) (retained : ∀ row ∈ h, row ∈ fresh) :
    MarginalsRecorded m fresh :=
  fun target x distinct => retained _ (recorded target x distinct)

theorem conditionalPlan_valid {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] {S : Type v}
    (source : S → FiniteSource X) (response : S → ElementaryAction X T → Bool)
    (exactResponse : ExactResponse source response)
    (conditional : Enumeration (ConditionalIndex T)) (m : X → X → Bool)
    (h : TranscriptDecoder.History X T) (recorded : MarginalsRecorded m h)
    (observedRows : ∀ q : ObservedIndex T, CoversAction h (observedIndexAction T m q)) :
    Valid (sourceGame T source response) (conditionalPlan T conditional m h) h
      (0 + conditional.items.length) := by
  apply collect_valid (fun _ => True) (fun s => classTarget T (source s)) response (LegalAction T)
    conditional.items conditional.nodup (conditionalIndexAction T m)
    (fun q _ => indicator_action_legal T m q.1.val.1 q.1.val.2 q.2)
  intro replies fresh facts
  change ∀ s, Consistent (sourceGame T source response) fresh s →
    classTarget T (source s) = decodeHistory T fresh
  intro s consistent
  apply (decoder_equals_classTarget T (source s) m fresh
    (recorded_retained m h fresh recorded facts.retained) ?_
    ((game_consistent_iff T source response exactResponse fresh s).mp consistent)).symm
  constructor
  · intro x y ordered W
    let q : ObservedIndex T := ⟨⟨(x, y), ordered⟩, W⟩
    obtain ⟨answer, member⟩ := observedRows q
    exact ⟨answer, facts.retained _ member⟩
  · intro target x distinct W
    let q : ConditionalIndex T := ⟨⟨(target, x), distinct⟩, W⟩
    exact ⟨replies q, facts.answered q (conditional.complete q)⟩

theorem observedPlan_valid {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] {S : Type v}
    (source : S → FiniteSource X) (response : S → ElementaryAction X T → Bool)
    (exactResponse : ExactResponse source response)
    (observed : Enumeration (ObservedIndex T)) (conditional : Enumeration (ConditionalIndex T))
    (m : X → X → Bool) (h : TranscriptDecoder.History X T) (recorded : MarginalsRecorded m h) :
    Valid (sourceGame T source response) (observedPlan T observed conditional m h) h
      ((0 + conditional.items.length) + observed.items.length) := by
  apply collect_valid (fun _ => True) (fun s => classTarget T (source s)) response (LegalAction T)
    observed.items observed.nodup (observedIndexAction T m)
    (fun q _ => pair_action_legal T m q.1.val.1 q.1.val.2 (ne_of_lt q.1.property) q.2)
  intro replies fresh facts
  apply conditionalPlan_valid T source response exactResponse conditional m fresh
    (recorded_retained m h fresh recorded facts.retained)
  intro q
  exact ⟨replies q, facts.answered q (observed.complete q)⟩

/-- Legality and remaining-budget validity quantify over ALL Boolean reply
branches, not only honest or reachable branches. Terminal soundness is
conditional on one source fitting the WHOLE final history, as in G7. -/
theorem restrictedPlanRaw_valid {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] {S : Type v}
    (source : S → FiniteSource X) (response : S → ElementaryAction X T → Bool)
    (exactResponse : ExactResponse source response)
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T)) :
    Valid (sourceGame T source response) (restrictedPlanRaw T marginals observed conditional) []
      (((0 + conditional.items.length) + observed.items.length) + marginals.items.length) := by
  apply collect_valid (fun _ => True) (fun s => classTarget T (source s)) response (LegalAction T)
    marginals.items marginals.nodup marginalIndexAction
    (fun q _ => marginal_action_legal q.val.1 q.val.2)
  intro replies fresh facts
  apply observedPlan_valid T source response exactResponse observed conditional
    (maskFromReplies T replies) fresh
  apply recorded_of_rows T replies fresh
  exact fun q => facts.answered q (marginals.complete q)

def reindexPlan {A : Type u} {Q : Type v} {m n : Nat} (same : m = n)
    (p : Plan A Bool Q m) : Plan A Bool Q n := same ▸ p

theorem reindexPlan_valid {S : Type*} {A : Type*} {Q : Type*} {R : Type*}
    (E : Experiment S A Bool Q R) {m n : Nat} (same : m = n)
    (p : Plan A Bool Q m) (h : GProgram.G7.ExactLawResourceGame.History A Bool) (resource : R)
    (valid : Valid E p h resource) : Valid E (reindexPlan same p) h resource := by
  subst n
  exact valid

theorem raw_budget_eq {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T]
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T)) :
    ((0 + conditional.items.length) + observed.items.length) + marginals.items.length =
      coordinateBudget T := by
  rw [marginals.length, observed.length, conditional.length]
  unfold coordinateBudget
  omega

def restrictedPlan {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T]
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T)) :
    Plan (ElementaryAction X T) Bool (Finset (TargetCode X T)) (coordinateBudget T) :=
  reindexPlan (raw_budget_eq T marginals observed conditional)
    (restrictedPlanRaw T marginals observed conditional)

theorem restrictedPlan_valid {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] {S : Type v}
    (source : S → FiniteSource X) (response : S → ElementaryAction X T → Bool)
    (exactResponse : ExactResponse source response)
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T)) :
    Valid (sourceGame T source response) (restrictedPlan T marginals observed conditional) []
      (coordinateBudget T) := by
  apply reindexPlan_valid
  rw [← raw_budget_eq T marginals observed conditional]
  exact restrictedPlanRaw_valid T source response exactResponse marginals observed conditional

/-- Uses explicit merge-sort enumerations from the supplied observed-label
order. This definition contains no classical finite-list choice or unknown
source evaluation. The returned plan is a finite response consumer. -/
def effectiveRestrictedPlan {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] :
    Plan (ElementaryAction X T) Bool (Finset (TargetCode X T)) (coordinateBudget T) :=
  restrictedPlan T (effectiveMarginalEnumeration T) (effectiveObservedEnumeration T)
    (effectiveConditionalEnumeration T)

theorem effectiveRestrictedPlan_valid {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] {S : Type v}
    (source : S → FiniteSource X) (response : S → ElementaryAction X T → Bool)
    (exactResponse : ExactResponse source response) :
    Valid (sourceGame T source response) (effectiveRestrictedPlan T) [] (coordinateBudget T) :=
  restrictedPlan_valid T source response exactResponse _ _ _

theorem effectiveRestrictedPlan_identifies_exact_response {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] {S : Type v}
    (source : S → FiniteSource X) (response : S → ElementaryAction X T → Bool)
    (exactResponse : ExactResponse source response) (s : S) :
    run (sourceGame T source response) (effectiveRestrictedPlan T) s = classTarget T (source s) := by
  apply valid_run_identifies (sourceGame T source response) (effectiveRestrictedPlan T) [] (coordinateBudget T)
  · exact effectiveRestrictedPlan_valid T source response exactResponse
  · exact ⟨True.intro, fun _ member => False.elim (List.not_mem_nil member)⟩

/-- The original source class, not just the registry. The same single D
generates each actual response in run. The exact class-target semantics
retains all observed labels, latent confounding and selected MAG marks. -/
theorem effectiveRestrictedPlan_identifies_original {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (D : FiniteSource X) :
    run (originalGame T) (effectiveRestrictedPlan T) D = classTarget T D := by
  apply valid_run_identifies (originalGame T) (effectiveRestrictedPlan T) [] (coordinateBudget T)
  · exact effectiveRestrictedPlan_valid T id (fun E a => graphicalReply E a) (original_response_exact T)
  · exact ⟨True.intro, fun _ member => False.elim (List.not_mem_nil member)⟩

theorem effectiveRestrictedPlan_identifies_registry {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (c : RegistryCode X) :
    run (registryGame T) (effectiveRestrictedPlan T) c = classTarget T (codeSource c) := by
  apply valid_run_identifies (registryGame T) (effectiveRestrictedPlan T) [] (coordinateBudget T)
  · exact effectiveRestrictedPlan_valid T codeSource (fun c a => codeAnswer c a) (registry_response_exact T)
  · exact ⟨True.intro, fun _ member => False.elim (List.not_mem_nil member)⟩

/-- Expanded final target contract. E is one ORIGINAL finite source across
the baseline and all available interventions, before its full marked TCM
is taken. Nothing is replaced by independent single-indicator classes. -/
theorem effectiveRestrictedPlan_full_target {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (D : FiniteSource X)
    (G : MarkedGraph (CombinedVertex X T)) :
    (∃ b ∈ run (originalGame T) (effectiveRestrictedPlan T) D, decodeTarget b = G) ↔
      ∃ E : FiniteSource X, SameSetwiseSignature T D E ∧ tcm E.dag T = G := by
  rw [effectiveRestrictedPlan_identifies_original]
  exact classTarget_image_exact T D G

end RestrictedCausal.PartialQueries
