import OriginalCalendarPattern
import FiniteCutSourceWord

/-! Stable symbolic cut insertion. Actual semantics are obtained by proving
agreement with the already verified physical one-cut compiler. -/
namespace UnifiedLean.G6.StableCutSchema
open Nanuq.Source GProgram.G5
open UnifiedLean.G6.NaturalCellInverseRates UnifiedLean.G6.OriginalCalendarSchema
open UnifiedLean.G6.FiniteCutSourceWord
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceProgramTransport
open scoped Classical

inductive Anchored {V E Tag : Type*} : AgeAtom V → List (Step V E × Tag) → AgeAtom V → Prop
  | nil (a) : Anchored a [] a
  | interval (a b c) (tag : Tag) (ws) : Anchored b ws c →
      Anchored a ((.interval a b,tag)::ws) c
  | exit (a c) (e : E) (tag : Tag) (ws) : Anchored a ws c →
      Anchored a ((.exit e,tag)::ws) c
  | enter (a c) (v : V) (tag : Tag) (ws) : Anchored a ws c →
      Anchored a ((.enter v,tag)::ws) c

def Ordered {V E Tag : Type*} (age : V → ℝ) (ws : List (Step V E × Tag)) : Prop :=
  ∀ a b tag, (.interval a b,tag) ∈ ws → a.eval age ≤ b.eval age

noncomputable def oneCut {V E Tag : Type*} (age : V → ℝ) (q : ℚ) :
    List (Step V E × Tag) → List (Step V E × (Tag × Bool))
  | [] => []
  | (.exit e,tag)::ws => (.exit e,(tag,false))::oneCut age q ws
  | (.enter v,tag)::ws => (.enter v,(tag,false))::oneCut age q ws
  | (.interval a b,tag)::ws =>
      if a.eval age < q ∧ (q:ℝ) < b.eval age then
        (.interval a (.fixed q),(tag,false))::(.interval (.fixed q) b,(tag,true))::oneCut age q ws
      else (.interval a b,(tag,decide ((q:ℝ) ≤ a.eval age)))::oneCut age q ws

variable {V E X Tag : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

noncomputable def interpret (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (ws : List (Step V E × Tag)) : List (ProgramStep N × Tag) :=
  ws.map (fun z => (instantiateStep N C H p common z.1,z.2))

 theorem one_cut_agrees (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (q : ℚ) {a z : AgeAtom V} {ws : List (Step V E × Tag)}
    (ha : Anchored a ws z) (ho : Ordered C.age ws) :
    interpret N C H p common (oneCut C.age q ws) =
      oneCutWord N q (interpret N C H p common ws) (a.eval C.age) := by
  induction ha with
  | nil a => rfl
  | exit a c e tag ws ha ih =>
    have ht : Ordered C.age ws := fun x y t hm => ho x y t (List.mem_cons_of_mem _ hm)
    simpa [oneCut,interpret,instantiateStep,oneCutWord] using congrArg
      (fun xs => (ProgramStep.boundary (.exit e),(tag,false))::xs) (ih ht)
  | enter a c v tag ws ha ih =>
    have ht : Ordered C.age ws := fun x y t hm => ho x y t (List.mem_cons_of_mem _ hm)
    simpa [oneCut,interpret,instantiateStep,oneCutWord] using congrArg
      (fun xs => (ProgramStep.boundary (originalNodeOperation N H (originalGamma p) common v),(tag,false))::xs) (ih ht)
  | interval a b c tag ws ha ih =>
    have hab := ho a b tag (by simp)
    have ht : Ordered C.age ws := fun x y t hm => ho x y t (List.mem_cons_of_mem _ hm)
    have hd : (Real.toNNReal (b.eval C.age-a.eval C.age) : ℝ) = b.eval C.age-a.eval C.age :=
      Real.coe_toNNReal _ (sub_nonneg.mpr hab)
    have hend : a.eval C.age+(b.eval C.age-a.eval C.age)=b.eval C.age := by ring
    simp only [oneCut,interpret,List.map_cons,instantiateStep,oneCutWord,hd,hend]
    split <;> simp_all [interpret,AgeAtom.eval,instantiateStep]

 theorem one_cut_anchored (age : V → ℝ) (q : ℚ) {a z : AgeAtom V}
    {ws : List (Step V E × Tag)} (ha : Anchored a ws z) :
    Anchored a (oneCut age q ws) z := by
  induction ha with
  | nil a => exact .nil a
  | exit a c e tag ws ha ih => exact .exit a c e (tag,false) _ ih
  | enter a c v tag ws ha ih => exact .enter a c v (tag,false) _ ih
  | interval a b c tag ws ha ih =>
    unfold oneCut
    split
    · exact .interval a (.fixed q) c (tag,false) _
        (.interval (.fixed q) b c (tag,true) _ ih)
    · exact .interval a b c _ _ ih

 theorem one_cut_ordered (age : V → ℝ) (q : ℚ) (ws : List (Step V E × Tag))
    (ho : Ordered age ws) : Ordered age (oneCut age q ws) := by
  induction ws with
  | nil => intro a b tag hm; simp [oneCut] at hm
  | cons w ws ih =>
    have ht := ih (fun a b tag hm => ho a b tag (List.mem_cons_of_mem _ hm))
    rcases w with ⟨op,tag⟩
    cases op with
    | exit e => simpa [Ordered,oneCut] using ht
    | enter v => simpa [Ordered,oneCut] using ht
    | interval a b =>
      have hab := ho a b tag (by simp)
      intro x y t hm
      by_cases hcut : a.eval age < q ∧ (q:ℝ) < b.eval age
      · simp only [oneCut,if_pos hcut,List.mem_cons] at hm
        rcases hm with he | he | hm
        · cases he; exact hcut.1.le
        · cases he; exact hcut.2.le
        · exact ht x y t hm
      · simp only [oneCut,if_neg hcut,List.mem_cons] at hm
        rcases hm with he | hm
        · cases he; exact hab
        · exact ht x y t hm

 theorem one_cut_stable {age age' : V → ℝ} (q : ℚ) (ws : List (Step V E × Tag))
    (hc : ∀ a b tag, (.interval a b,tag) ∈ ws →
      (a.eval age < (q:ℝ) ↔ a.eval age' < (q:ℝ)) ∧
      ((q:ℝ) < b.eval age ↔ (q:ℝ) < b.eval age') ∧
      ((q:ℝ) ≤ a.eval age ↔ (q:ℝ) ≤ a.eval age')) :
    oneCut age q ws = oneCut age' q ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have ht := ih (fun a b tag hm => hc a b tag (List.mem_cons_of_mem _ hm))
    rcases w with ⟨op,tag⟩
    cases op with
    | exit e => simp [oneCut,ht]
    | enter v => simp [oneCut,ht]
    | interval a b =>
      rcases hc a b tag (by simp) with ⟨h1,h2,h3⟩
      simp only [oneCut,ht,h1,h2,h3]

open UnifiedLean.G6.GeneratedNaturalChronology

def Available {j : ℕ} (cuts : Fin j → ℚ) (a : AgeAtom V) : Prop :=
  ∃ e : Event V j, atom cuts e = a

 theorem available_lt {j : ℕ} (cuts : Fin j → ℚ) (sig : Signature V j)
    {age age' : V → ℝ} (h : Realizes cuts sig age) (h' : Realizes cuts sig age')
    {a b : AgeAtom V} (ha : Available cuts a) (hb : Available cuts b) :
    a.eval age < b.eval age ↔ a.eval age' < b.eval age' := by
  obtain ⟨i,rfl⟩ := ha
  obtain ⟨k,rfl⟩ := hb
  exact (before_iff h i k).symm.trans (before_iff h' i k)

 theorem available_le {j : ℕ} (cuts : Fin j → ℚ) (sig : Signature V j)
    {age age' : V → ℝ} (h : Realizes cuts sig age) (h' : Realizes cuts sig age')
    {a b : AgeAtom V} (ha : Available cuts a) (hb : Available cuts b) :
    a.eval age ≤ b.eval age ↔ a.eval age' ≤ b.eval age' := by
  obtain ⟨i,rfl⟩ := ha
  obtain ⟨k,rfl⟩ := hb
  exact (atMost_iff h i k).symm.trans (atMost_iff h' i k)

 theorem one_cut_available {j : ℕ} (cuts : Fin j → ℚ) (age : V → ℝ)
    (k : Fin j) (ws : List (Step V E × Tag))
    (hw : ∀ a b tag, (.interval a b,tag) ∈ ws → Available cuts a ∧ Available cuts b) :
    ∀ a b tag, (.interval a b,tag) ∈ oneCut age (cuts k) ws →
      Available cuts a ∧ Available cuts b := by
  have hq : Available (V := V) cuts (.fixed (cuts k)) := ⟨.inr k,rfl⟩
  induction ws with
  | nil => intro a b tag hm; simp [oneCut] at hm
  | cons w ws ih =>
    have ht := ih (fun a b tag hm => hw a b tag (List.mem_cons_of_mem _ hm))
    rcases w with ⟨op,tag⟩
    cases op with
    | exit e => simpa [oneCut] using ht
    | enter v => simpa [oneCut] using ht
    | interval a b =>
      have hab := hw a b tag (by simp)
      intro x y t hm
      by_cases hcut : a.eval age < cuts k ∧ (cuts k:ℝ) < b.eval age
      · simp only [oneCut,if_pos hcut,List.mem_cons] at hm
        rcases hm with he | he | hm
        · cases he; exact ⟨hab.1,hq⟩
        · cases he; exact ⟨hq,hab.2⟩
        · exact ht x y t hm
      · simp only [oneCut,if_neg hcut,List.mem_cons] at hm
        rcases hm with he | hm
        · cases he; exact hab
        · exact ht x y t hm

 theorem realized_one_cut_stable {j : ℕ} (cuts : Fin j → ℚ) (sig : Signature V j)
    {age age' : V → ℝ} (h : Realizes cuts sig age) (h' : Realizes cuts sig age')
    (k : Fin j) (ws : List (Step V E × Tag))
    (hw : ∀ a b tag, (.interval a b,tag) ∈ ws → Available cuts a ∧ Available cuts b) :
    oneCut age (cuts k) ws = oneCut age' (cuts k) ws := by
  apply one_cut_stable
  intro a b tag hm
  obtain ⟨ha,hb⟩ := hw a b tag hm
  have hq : Available (V := V) cuts (.fixed (cuts k)) := ⟨.inr k,rfl⟩
  exact ⟨available_lt cuts sig h h' ha hq,available_lt cuts sig h h' hq hb,
    available_le cuts sig h h' hq ha⟩

end UnifiedLean.G6.StableCutSchema
