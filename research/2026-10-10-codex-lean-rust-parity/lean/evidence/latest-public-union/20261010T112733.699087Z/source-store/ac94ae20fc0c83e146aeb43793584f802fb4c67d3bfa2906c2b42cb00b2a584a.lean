import UnifiedLean.Source.E8SCFG2BEOwnership

/-!
# Literal sparse scaffold partner writes and generated-emission binding

Public source: TakumiOtagaki/PKProbDesign27afdd054272dbda8a74c8aad156970a44c23cd8,
submodules/CParty/src/sparse_tree.cc105--109 (x=-1; symmetric closing writes),
scfg2/replay/w_final_exact_inside.hh332--337 (bounded table read), and
scfg2/engine/traceback_pairs.hh168--200 (directional fixed-pair filter).

The paper scaffold G is independently supplied. Admitted closing actions must
belong to G, cover G, and x writes must avoid its endpoints. The table relation
and generated-filter equality are derived, not fields. The actual lexical
stack-to-actions/executed-C++ refinement is still an explicit source gate.
-/
noncomputable section
open scoped Classical
namespace UnifiedLean.Source.E8SCFG2PartnerAdmission
open UnifiedLean.Source.E8PaperGammaAdmission
open UnifiedLean.Source.E8SCFG2RootEventDecoder
open UnifiedLean.Source.E8SCFG2BEOwnership

variable {n : ℕ}

def oneBased (i : Fin n) : ℤ := (i.val : ℤ) + 1

def Neighbors (G : Structure n) (i j : Fin n) : Prop :=
  (i,j) ∈ G ∨ (j,i) ∈ G

private theorem neighbor_symm (G : Structure n) (i j : Fin n) :
    Neighbors G i j ↔ Neighbors G j i := by
  simp [Neighbors, or_comm]

private theorem neighbor_at_left (seq : Fin n → Base) (G : Structure n)
    (hs : Secondary seq G) (p : Pair n) (hp : p ∈ G) (j : Fin n) :
    Neighbors G p.1 j ↔ j = p.2 := by
  constructor
  · intro h
    rcases h with h | h
    · by_cases he : p = (p.1,j)
      · exact (congrArg Prod.snd he).symm
      · have hd := hs.2 p hp (p.1,j) h he
        exact False.elim (hd.1 rfl)
    · by_cases he : p = (j,p.1)
      · have hlt := (hs.1 p hp).1
        have hlt' := (hs.1 (j,p.1) h).1
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        simp only at h1 h2
        omega
      · have hd := hs.2 p hp (j,p.1) h he
        exact False.elim (hd.2.1 rfl)
  · rintro rfl
    exact Or.inl hp

private theorem neighbor_at_right (seq : Fin n → Base) (G : Structure n)
    (hs : Secondary seq G) (p : Pair n) (hp : p ∈ G) (j : Fin n) :
    Neighbors G p.2 j ↔ j = p.1 := by
  constructor
  · intro h
    rcases h with h | h
    · by_cases he : p = (p.2,j)
      · have hlt := (hs.1 p hp).1
        have hlt' := (hs.1 (p.2,j) h).1
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        simp only at h1 h2
        omega
      · have hd := hs.2 p hp (p.2,j) h he
        exact False.elim (hd.2.2.1 rfl)
    · by_cases he : p = (j,p.2)
      · exact (congrArg Prod.fst he).symm
      · have hd := hs.2 p hp (j,p.2) h he
        exact False.elim (hd.2.2.2 rfl)
  · rintro rfl
    exact Or.inr hp

inductive PairAction (n : ℕ) where
  | close (pair : Pair n)
  | forcedUnpaired (position : Fin n)
  deriving DecidableEq

structure PairState (n : ℕ) where
  table : Fin n → ℤ
  closed : Structure n

def initialState (n : ℕ) : PairState n := ⟨fun _ => -2, ∅⟩

/-- The two actual close writes, and x's negative write. `closed` is a ghost
set for the proof and is not claimed to be stored by the C++ parser. -/
def writeAction (st : PairState n) : PairAction n → PairState n
  | .close p => ⟨Function.update (Function.update st.table p.2 (oneBased p.1))
      p.1 (oneBased p.2), insert p st.closed⟩
  | .forcedUnpaired i => ⟨Function.update st.table i (-1), st.closed⟩

def runActions (st : PairState n) : List (PairAction n) → PairState n
  | [] => st
  | a::as => runActions (writeAction st a) as

def ActionAllowed (G : Structure n) : PairAction n → Prop
  | .close p => p ∈ G
  | .forcedUnpaired i => ∀ p ∈ G, i ≠ p.1 ∧ i ≠ p.2

def TableRepresents (st : PairState n) : Prop :=
  ∀ i j : Fin n, st.table i = oneBased j ↔ Neighbors st.closed i j

private theorem initial_represents (n : ℕ) : TableRepresents (initialState n) := by
  intro i j
  simp [initialState, Neighbors, oneBased]
  omega

private theorem oneBased_injective {i j : Fin n} : oneBased i = oneBased j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    simp only [oneBased] at h
    omega
  · rintro rfl
    rfl

private theorem write_subset (G : Structure n) (st : PairState n) (a : PairAction n)
    (hsub : st.closed ⊆ G) (ha : ActionAllowed G a) :
    (writeAction st a).closed ⊆ G := by
  cases a with
  | close p => simpa [writeAction, ActionAllowed] using Finset.insert_subset ha hsub
  | forcedUnpaired i => exact hsub

private theorem write_represents (seq : Fin n → Base) (G : Structure n)
    (hs : Secondary seq G) (st : PairState n) (ht : TableRepresents st)
    (hsub : st.closed ⊆ G) (a : PairAction n) (ha : ActionAllowed G a) :
    TableRepresents (writeAction st a) := by
  cases a with
  | close p =>
    change p ∈ G at ha
    have hne : p.1 ≠ p.2 := ne_of_lt (hs.1 p ha).1
    have hsub' : insert p st.closed ⊆ G := Finset.insert_subset ha hsub
    intro i j
    by_cases hleft : i = p.1
    · subst i
      simp only [writeAction, Function.update_self]
      rw [oneBased_injective]
      constructor
      · rintro rfl
        exact Or.inl (Finset.mem_insert_self _ _)
      · intro h
        apply Eq.symm
        apply (neighbor_at_left seq G hs p ha j).mp
        rcases h with h | h
        · exact Or.inl (hsub' h)
        · exact Or.inr (hsub' h)
    · by_cases hright : i = p.2
      · subst i
        simp only [writeAction, Function.update_of_ne hleft, Function.update_self]
        rw [oneBased_injective]
        constructor
        · rintro rfl
          exact Or.inr (Finset.mem_insert_self _ _)
        · intro h
          apply Eq.symm
          apply (neighbor_at_right seq G hs p ha j).mp
          rcases h with h | h
          · exact Or.inl (hsub' h)
          · exact Or.inr (hsub' h)
      · simp only [writeAction, Function.update_of_ne hright, Function.update_of_ne hleft]
        rw [ht]
        simp only [Neighbors, Finset.mem_insert]
        constructor
        · intro h
          rcases h with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr (Or.inr h)
        · intro h
          rcases h with (h | h) | (h | h)
          · exact False.elim (hleft (congrArg Prod.fst h))
          · exact Or.inl h
          · exact False.elim (hright (congrArg Prod.snd h))
          · exact Or.inr h
  | forcedUnpaired k =>
    change ∀ p ∈ G, k ≠ p.1 ∧ k ≠ p.2 at ha
    intro i j
    by_cases he : i = k
    · subst i
      simp only [writeAction, Function.update_self]
      have hnone : ¬ Neighbors st.closed k j := by
        intro h
        rcases h with h | h
        · exact (ha (k,j) (hsub h)).1 rfl
        · exact (ha (j,k) (hsub h)).2 rfl
      simp only [hnone, iff_false]
      simp [oneBased]
      omega
    · simpa only [writeAction, Function.update_of_ne he] using ht i j

private theorem run_invariants (seq : Fin n → Base) (G : Structure n)
    (hs : Secondary seq G) (st : PairState n) (ht : TableRepresents st)
    (hsub : st.closed ⊆ G) (as : List (PairAction n))
    (ha : ∀ a ∈ as, ActionAllowed G a) :
    TableRepresents (runActions st as) ∧ (runActions st as).closed ⊆ G := by
  induction as generalizing st with
  | nil => exact ⟨ht,hsub⟩
  | cons a as ih =>
    apply ih (writeAction st a)
      (write_represents seq G hs st ht hsub a (ha a (by simp)))
      (write_subset G st a hsub (ha a (by simp)))
    intro b hb
    exact ha b (by simp [hb])

theorem closed_membership (st : PairState n) (as : List (PairAction n)) (p : Pair n) :
    p ∈ (runActions st as).closed ↔ p ∈ st.closed ∨ PairAction.close p ∈ as := by
  induction as generalizing st with
  | nil => simp [runActions]
  | cons a as ih =>
    rw [runActions, ih]
    cases a <;> simp [writeAction, or_assoc, or_left_comm]

/-- A primitive validated closing-action interface. G is already fixed by
independent PaperInput, rather than defined from an observed table/output. -/
structure ClosingAdmission (G : Structure n) where
  actions : List (PairAction n)
  allowed : ∀ a ∈ actions, ActionAllowed G a
  covers : ∀ p ∈ G, PairAction.close p ∈ actions

theorem admitted_table_represents (seq : Fin n → Base) (G : Structure n)
    (hs : Secondary seq G) (admit : ClosingAdmission G) :
    ∀ i j : Fin n, (runActions (initialState n) admit.actions).table i = oneBased j ↔
      Neighbors G i j := by
  have hi := run_invariants seq G hs (initialState n) (initial_represents n)
    (by simp [initialState]) admit.actions admit.allowed
  have hc : (runActions (initialState n) admit.actions).closed = G := by
    apply Finset.Subset.antisymm hi.2
    intro p hp
    rw [closed_membership]
    exact Or.inr (admit.covers p hp)
  intro i j
  simpa only [hc] using hi.1 i j

/-- Actual context's range-checked lookup, with exact (x-1).toNat indexing. -/
def partnerFromTable (table : Fin n → ℤ) (x : ℤ) : ℤ :=
  if hx : 1 ≤ x ∧ x ≤ (n : ℤ) then table (positionIndex n x hx.1 hx.2) else -1

private theorem partner_oneBased (table : Fin n → ℤ) (i : Fin n) :
    partnerFromTable table (oneBased i) = table i := by
  have hdom : 1 ≤ oneBased i ∧ oneBased i ≤ (n : ℤ) := by
    simp only [oneBased]
    constructor <;> omega
  simp only [partnerFromTable, dif_pos hdom]
  congr 1
  apply Fin.ext
  simp [positionIndex, oneBased]

/-- The directional source fixed-pair test equals membership in independent
ordered G; the equivalence is a derived result of writes/coverage/matching. -/
theorem fixed_pair_iff_scaffold (seq : Fin n → Base) (G : Structure n)
    (hs : Secondary seq G) (admit : ClosingAdmission G) (p : Pair n) (hp : p.1 < p.2) :
    PartnerPair (partnerFromTable (runActions (initialState n) admit.actions).table)
      (oneBased p.1) (oneBased p.2) ↔ p ∈ G := by
  rw [PartnerPair, partner_oneBased, partner_oneBased,
    admitted_table_represents seq G hs admit, admitted_table_represents seq G hs admit]
  rw [← neighbor_symm G p.1 p.2, or_self]
  constructor
  · rintro (h | h)
    · exact h
    · have hrev : p.2 < p.1 := (hs.1 (p.2,p.1) h).1
      omega
  · exact Or.inl

/-- Literal four-family source helper, expressed on bounded source events. -/
def SourceEmitsGenerated (partner : ℤ → ℤ) (e : SourceEvent n) : Prop :=
  (e.family = .V ∨ e.family = .VP ∨ e.family = .VP_CLOSED ∨ e.family = .VP_DIRECT) ∧
    ¬ PartnerPair partner (oneBased e.pair.1) (oneBased e.pair.2)

theorem generated_filter_agreement (seq : Fin n → Base) (G : Structure n)
    (hs : Secondary seq G) (admit : ClosingAdmission G) (e : SourceEvent n)
    (he : e.pair.1 < e.pair.2) :
    SourceEmitsGenerated (partnerFromTable (runActions (initialState n) admit.actions).table) e ↔
      EmitsGenerated G e := by
  simp only [SourceEmitsGenerated, EmitsGenerated,
    fixed_pair_iff_scaffold seq G hs admit e.pair he]

/-- Set projection of the source helper's append_unique square-lane output.
Vector order/renderer lanes remain a separate lossless-rendering contract. -/
def sourceGeneratedPairs (partner : ℤ → ℤ) : List (SourceEvent n) → Structure n
  | [] => ∅
  | e::es => if SourceEmitsGenerated partner e then
      insert e.pair (sourceGeneratedPairs partner es) else sourceGeneratedPairs partner es

/-- Only the four emitting families need a strict pair. Non-emitting W/WI
nodes may have singleton intervals, so no unnecessary all-event strictness. -/
def EmissionDomain (events : List (SourceEvent n)) : Prop :=
  ∀ e ∈ events,
    (e.family = .V ∨ e.family = .VP ∨ e.family = .VP_CLOSED ∨ e.family = .VP_DIRECT) →
      e.pair.1 < e.pair.2

/-- The complete generated-emission set now matches the independent Γ
observable once primitive partner writes and actual emitting-family bounds
are admitted. This is not an assumed observable/probability equality field. -/
theorem generated_stream_agreement (seq : Fin n → Base) (G : Structure n)
    (hs : Secondary seq G) (admit : ClosingAdmission G) (events : List (SourceEvent n))
    (hd : EmissionDomain events) :
    sourceGeneratedPairs (partnerFromTable (runActions (initialState n) admit.actions).table) events =
      generatedPairs G events := by
  induction events with
  | nil => rfl
  | cons e es ih =>
    have heq : SourceEmitsGenerated
        (partnerFromTable (runActions (initialState n) admit.actions).table) e ↔ EmitsGenerated G e := by
      by_cases he : e.family = .V ∨ e.family = .VP ∨ e.family = .VP_CLOSED ∨ e.family = .VP_DIRECT
      · exact generated_filter_agreement seq G hs admit e (hd e (by simp) he)
      · simp [SourceEmitsGenerated, EmitsGenerated, he]
    have htail : EmissionDomain es := fun x hx => hd x (by simp [hx])
    simp only [sourceGeneratedPairs, generatedPairs, heq, ih htail]

/-- Converts an already owned source pair into actual independent scaffold
membership with exact 1-based coordinates. No clipping or scaffold redefinition. -/
theorem owned_bound_pair_in_scaffold (seq : Fin n → Base) (G : Structure n)
    (hs : Secondary seq G) (admit : ClosingAdmission G) (x y : ℤ)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hxn : x ≤ (n : ℤ)) (hyn : y ≤ (n : ℤ))
    (hxy : x < y)
    (ho : PartnerPair (partnerFromTable (runActions (initialState n) admit.actions).table) x y) :
    (positionIndex n x hx hxn, positionIndex n y hy hyn) ∈ G := by
  have hleft := positionIndex_roundtrip n x hx hxn
  have hright := positionIndex_roundtrip n y hy hyn
  apply (fixed_pair_iff_scaffold seq G hs admit
    (positionIndex n x hx hxn, positionIndex n y hy hyn) (by
      change (positionIndex n x hx hxn).val < (positionIndex n y hy hyn).val
      omega)).mp
  simpa only [oneBased, hleft, hright] using ho

#print axioms closed_membership
#print axioms admitted_table_represents
#print axioms fixed_pair_iff_scaffold
#print axioms generated_filter_agreement
#print axioms generated_stream_agreement
#print axioms owned_bound_pair_in_scaffold
end UnifiedLean.Source.E8SCFG2PartnerAdmission
