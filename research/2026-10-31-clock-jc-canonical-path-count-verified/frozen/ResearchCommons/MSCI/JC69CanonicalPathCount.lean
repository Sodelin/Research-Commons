import ResearchCommons.MSCI.JC69UnorderedContinuation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.OfFn

/-! Original-copy minimum-block labels and a genuine canonical path-word
injection. UNCOMPILED, dot (OpenAI), 31 October 2026. Count the actual canonical
subtype of the accepted OrderedPath, not an assumed E-sized source quotient.
The weighted source identification of the canonical sum remains separate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69CanonicalPathCount
open Nanuq.Source GProgram.SourceForest GProgram.G2.FaithfulPairAgeDecoration
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open ResearchCommons.MSCI.JC69CurrentPartition ResearchCommons.MSCI.JC69SourceRootQuotient
open ResearchCommons.MSCI.JC69OrderedPathExpansion ResearchCommons.MSCI.JC69UnorderedContinuation
open scoped Classical BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Minimum ENUMERATED ORIGINAL copy of the complete descendant block.
No claim that the surviving raw representative itself is its minimum. -/
def blockRank {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (a : Copy) : Fin n :=
  (((state s).genealogy a).leaves.image e).min'
    (Finset.image_nonempty.mpr ⟨witness ((state s).genealogy a),witness_mem _⟩)

lemma blockRank_member {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (a : Copy) :
    e.symm (blockRank e N s a) ∈ ((state s).genealogy a).leaves := by
  have h : blockRank e N s a ∈ ((state s).genealogy a).leaves.image e := Finset.min'_mem _ _
  obtain ⟨x,hx,he⟩ := Finset.mem_image.mp h
  rw [← he]
  simpa using hx

lemma blockRank_live_injective {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) {a b : Copy}
    (ha : a ∈ (state s).live) (hb : b ∈ (state s).live)
    (he : blockRank e N s a = blockRank e N s b) : a = b := by
  have hma := blockRank_member e N s a
  have hmb := blockRank_member e N s b
  rw [← he] at hmb
  exact ((s.property.forest.leaf_fiber a ha _).mp hma).symm.trans
    ((s.property.forest.leaf_fiber b hb _).mp hmb)

lemma choice_blockRanks_ne {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (p : Choice N s) :
    blockRank e N s p.2.val.1 ≠ blockRank e N s p.2.val.2 := by
  intro he
  obtain ⟨ha,hb,hab⟩ := Finset.mem_offDiag.mp p.2.property
  exact hab (blockRank_live_injective e N s (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 he)

def IsCanonical {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (p : Choice N s) : Prop :=
  blockRank e N s p.2.val.1 < blockRank e N s p.2.val.2

abbrev CanonicalChoice {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) := {p : Choice N s // IsCanonical e N s p}

lemma canonical_reverse_iff {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (p : Choice N s) :
    IsCanonical e N s (reverseChoice N s p) ↔ ¬ IsCanonical e N s p := by
  change blockRank e N s p.2.val.2 < blockRank e N s p.2.val.1 ↔
    ¬ blockRank e N s p.2.val.1 < blockRank e N s p.2.val.2
  constructor
  · intro h h'
    exact (not_lt_of_ge h.le) h'
  · intro h
    exact lt_of_le_of_ne (le_of_not_gt h) (choice_blockRanks_ne e N s p).symm

/-- The common alphabet has no population/register component. -/
abbrev PairAlphabet (n : ℕ) := {A : Finset (Fin n) // A.card = 2}

lemma pairAlphabet_card (n : ℕ) : Fintype.card (PairAlphabet n) = n.choose 2 := by
  let e : PairAlphabet n ≃ ↥((Finset.univ : Finset (Fin n)).powersetCard 2) :=
    Equiv.subtypeEquivRight (fun A => by simp)
  rw [Fintype.card_congr e,Fintype.card_coe,Finset.card_powersetCard]
  simp

def pairLabel {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (p : Choice N s) : PairAlphabet n :=
  ⟨{blockRank e N s p.2.val.1,blockRank e N s p.2.val.2},by simp [choice_blockRanks_ne e N s p]⟩

lemma originalPlace_injective (N : RootedBinary V E X) : Function.Injective (originalPlace N) := by
  intro i j h
  cases i <;> cases j <;> simpa [originalPlace] using h

/-- Same two minimum-block labels identify an ACTUAL canonical Choice,
including its original population, not just its raw pair or observation. -/
theorem canonical_pairLabel_injective {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) :
    Function.Injective (fun p : CanonicalChoice e N s => pairLabel e N s p.val) := by
  intro p q he
  rcases p with ⟨⟨i,⟨⟨a,b⟩,hp⟩⟩,hpc⟩
  rcases q with ⟨⟨j,⟨⟨c,d⟩,hq⟩⟩,hqc⟩
  have hset := congrArg Subtype.val he
  change ({blockRank e N s a,blockRank e N s b} : Finset (Fin n)) =
    {blockRank e N s c,blockRank e N s d} at hset
  have ha : blockRank e N s a = blockRank e N s c ∨ blockRank e N s a = blockRank e N s d := by
    have hm : blockRank e N s a ∈ ({blockRank e N s c,blockRank e N s d} : Finset (Fin n)) := by
      rw [← hset]; simp
    simpa using hm
  have hb : blockRank e N s b = blockRank e N s c ∨ blockRank e N s b = blockRank e N s d := by
    have hm : blockRank e N s b ∈ ({blockRank e N s c,blockRank e N s d} : Finset (Fin n)) := by
      rw [← hset]; simp
    simpa using hm
  change blockRank e N s a < blockRank e N s b at hpc
  change blockRank e N s c < blockRank e N s d at hqc
  have hac : blockRank e N s a = blockRank e N s c := by rcases ha with h | h <;> rcases hb with h' | h' <;> omega
  have hbd : blockRank e N s b = blockRank e N s d := by rcases ha with h | h <;> rcases hb with h' | h' <;> omega
  obtain ⟨hal,hbl,hab⟩ := Finset.mem_offDiag.mp hp
  obtain ⟨hcl,hdl,hcd⟩ := Finset.mem_offDiag.mp hq
  have ac := blockRank_live_injective e N s (Finset.mem_filter.mp hal).1 (Finset.mem_filter.mp hcl).1 hac
  have bd := blockRank_live_injective e N s (Finset.mem_filter.mp hbl).1 (Finset.mem_filter.mp hdl).1 hbd
  subst c
  subst d
  have hi : i = j := originalPlace_injective N ((Finset.mem_filter.mp hal).2.symm.trans (Finset.mem_filter.mp hcl).2)
  subst j
  rfl

theorem canonical_choice_card_le {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) :
    Fintype.card (CanonicalChoice e N s) ≤ n.choose 2 := by
  rw [← pairAlphabet_card]
  exact Fintype.card_le_of_injective _ (canonical_pairLabel_injective e N s)

/-- Canonicality is checked at EACH original coded destination. -/
def CanonicalPathPred {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} : (fuel : ℕ) → (s : Code N sample) → OrderedPath N fuel s → Prop
  | 0, _, _ => True
  | _+1, _, .inl _ => True
  | fuel+1, s, .inr ⟨p,h⟩ => IsCanonical e N s p ∧ CanonicalPathPred e N fuel (stepDestination N s (some p)) h

abbrev CanonicalPath {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : ℕ) (s : Code N sample) :=
  {h : OrderedPath N fuel s // CanonicalPathPred e N fuel s h}

def pathWord {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} : (fuel : ℕ) → (s : Code N sample) → OrderedPath N fuel s → List (PairAlphabet n)
  | 0, _, _ => []
  | _+1, _, .inl _ => []
  | fuel+1, s, .inr ⟨p,h⟩ => pairLabel e N s p :: pathWord e N fuel (stepDestination N s (some p)) h

lemma pathWord_length {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : ℕ) (s : Code N sample) (h : OrderedPath N fuel s) :
    (pathWord e N fuel s h).length = pathLength N fuel s h := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      cases h with
      | inl h => rfl
      | inr h => obtain ⟨p,h⟩ := h; simp [pathWord,pathLength,ih,Nat.add_comm]

/-- A word reconstructs its actual canonical path from the fixed initial
Code and fuel. No representative/history equivalence is assumed. -/
theorem canonical_pathWord_injective {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : ℕ) (s : Code N sample) :
    Function.Injective (fun h : CanonicalPath e N fuel s => pathWord e N fuel s h.val) := by
  have H : ∀ fuel, ∀ s : Code N sample, ∀ h k : OrderedPath N fuel s,
      CanonicalPathPred e N fuel s h → CanonicalPathPred e N fuel s k →
      pathWord e N fuel s h = pathWord e N fuel s k → h = k := by
    intro fuel
    induction fuel with
    | zero => intro s h k _ _ _; exact Subsingleton.elim _ _
    | succ fuel ih =>
        intro s h k hh hk he
        cases h with
        | inl h =>
            cases k with
            | inl k => congr 1; exact Subsingleton.elim _ _
            | inr k => simp [pathWord] at he
        | inr h =>
            cases k with
            | inl k => simp [pathWord] at he
            | inr k =>
                obtain ⟨p,h⟩ := h
                obtain ⟨q,k⟩ := k
                have he' := List.cons.inj he
                have hpq : p = q := congrArg Subtype.val
                  (canonical_pairLabel_injective e N s ⟨p,hh.1⟩ ⟨q,hk.1⟩ he'.1)
                subst q
                have hhk := ih (stepDestination N s (some p)) h k hh.2 hk.2 he'.2
                subst k
                rfl
  intro h k he
  apply Subtype.ext
  exact H fuel s h.val k.val h.property k.property he

/-- All bounded words, including invalid ones as harmless overcount. -/
abbrev BoundedWords (n : ℕ) := Σ k : Fin n, Fin k.val → PairAlphabet n

lemma boundedWords_card (n : ℕ) :
    Fintype.card (BoundedWords n) = ∑ k ∈ Finset.range n, (n.choose 2)^k := by
  simp only [BoundedWords,Fintype.card_sigma,Fintype.card_fun,Fintype.card_fin,pairAlphabet_card]
  exact Fin.sum_univ_eq_sum_range (fun k => (n.choose 2)^k) n

def boundedWord [Nonempty Copy] (e : Copy ≃ Fin (Fintype.card Copy)) (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : ℕ) (s : Code N sample) (h : CanonicalPath e N fuel s) :
    BoundedWords (Fintype.card Copy) :=
  ⟨⟨(pathWord e N fuel s h.val).length,by
    rw [pathWord_length]
    exact pathLength_lt_original_copies N fuel s h.val⟩,
    (pathWord e N fuel s h.val).get⟩

lemma boundedWord_injective [Nonempty Copy] (e : Copy ≃ Fin (Fintype.card Copy))
    (N : RootedBinary V E X) {sample : Copy → X} (fuel : ℕ) (s : Code N sample) :
    Function.Injective (boundedWord e N fuel s) := by
  intro h k he
  apply canonical_pathWord_injective e N fuel s
  have hm := congrArg (fun w : BoundedWords (Fintype.card Copy) => List.ofFn w.2) he
  simpa only [boundedWord,List.ofFn_get] using hm

/-- EXACT original E bound for actual canonical paths, not for all ordered
paths. n counts original copies; the finite fuel may be arbitrarily large. -/
theorem actual_canonical_path_card_le [Nonempty Copy]
    (e : Copy ≃ Fin (Fintype.card Copy)) (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : ℕ) (s : Code N sample) :
    Fintype.card (CanonicalPath e N fuel s) ≤
      ∑ k ∈ Finset.range (Fintype.card Copy), ((Fintype.card Copy).choose 2)^k := by
  rw [← boundedWords_card]
  exact Fintype.card_le_of_injective _ (boundedWord_injective e N fuel s)

/-- The enumeration is available internally, not an extra scientific premise. -/
theorem actual_source_canonical_path_bound [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : ℕ) (s : Code N sample) :
    Fintype.card (CanonicalPath (Fintype.equivFin Copy) N fuel s) ≤
      ∑ k ∈ Finset.range (Fintype.card Copy), ((Fintype.card Copy).choose 2)^k :=
  actual_canonical_path_card_le (Fintype.equivFin Copy) N fuel s

#print axioms canonical_pairLabel_injective
#print axioms canonical_choice_card_le
#print axioms canonical_pathWord_injective
#print axioms boundedWords_card
#print axioms actual_canonical_path_card_le
#print axioms actual_source_canonical_path_bound
end ResearchCommons.MSCI.JC69CanonicalPathCount
