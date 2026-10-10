import StableCutSchema

/-! Finite symbolic cut words and their actual physical interpretation. -/
namespace UnifiedLean.G6.StableFiniteCutSchema
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.G6.NaturalCellInverseRates UnifiedLean.G6.OriginalCalendarSchema
open UnifiedLean.G6.StableCutSchema UnifiedLean.G6.GeneratedNaturalChronology
open UnifiedLean.G6.FiniteCutSourceWord
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeIndependentPairMixture
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

def values {j : ℕ} (cuts : Fin j → ℚ) (ks : List (Fin j)) : List ℝ :=
  ks.map (fun k => (cuts k:ℝ))

noncomputable def word {j : ℕ} (age : V → ℝ) (cuts : Fin j → ℚ) :
    (ks : List (Fin j)) → List (Step V E) → List (Step V E × CutTags (values cuts ks))
  | [],schema => schema.map (fun s => (s,()))
  | k::ks,schema => oneCut age (cuts k) (word age cuts ks schema)

 theorem word_anchored {j : ℕ} (age : V → ℝ) (cuts : Fin j → ℚ)
    (ks : List (Fin j)) (schema : List (Step V E)) (a z : AgeAtom V)
    (ha : Anchored a (schema.map (fun s => (s,()))) z) :
    Anchored a (word age cuts ks schema) z := by
  induction ks with
  | nil => exact ha
  | cons k ks ih => exact one_cut_anchored age (cuts k) ih

 theorem word_ordered {j : ℕ} (age : V → ℝ) (cuts : Fin j → ℚ)
    (ks : List (Fin j)) (schema : List (Step V E))
    (ho : Ordered age (schema.map (fun s => (s,())))) :
    Ordered age (word age cuts ks schema) := by
  induction ks with
  | nil => exact ho
  | cons k ks ih => exact one_cut_ordered age (cuts k) _ ih

 theorem word_available {j : ℕ} (age : V → ℝ) (cuts : Fin j → ℚ)
    (ks : List (Fin j)) (schema : List (Step V E))
    (hs : ∀ a b, Step.interval a b ∈ schema → Available cuts a ∧ Available cuts b) :
    ∀ a b tag, (.interval a b,tag) ∈ word age cuts ks schema →
      Available cuts a ∧ Available cuts b := by
  induction ks with
  | nil =>
    intro a b tag hm
    obtain ⟨s,hmem,he⟩ := List.mem_map.mp hm
    have he' := congrArg Prod.fst he
    change s = Step.interval a b at he'
    subst s
    exact hs a b hmem
  | cons k ks ih => exact one_cut_available cuts age k _ ih

 theorem word_stable {j : ℕ} (cuts : Fin j → ℚ) (sig : Signature V j)
    {age age' : V → ℝ} (h : Realizes cuts sig age) (h' : Realizes cuts sig age')
    (ks : List (Fin j)) (schema : List (Step V E))
    (hs : ∀ a b, Step.interval a b ∈ schema → Available cuts a ∧ Available cuts b) :
    word age cuts ks schema = word age' cuts ks schema := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    exact (realized_one_cut_stable cuts sig h h' k _
      (word_available age cuts ks schema hs)).trans
      (congrArg (oneCut age' (cuts k)) ih)

 theorem word_agrees (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    {j : ℕ} (cuts : Fin j → ℚ) (ks : List (Fin j)) (schema : List (Step V E))
    (a z : AgeAtom V) (ha : Anchored a (schema.map (fun s => (s,()))) z)
    (ho : Ordered C.age (schema.map (fun s => (s,())))) :
    interpret N C H p common (word C.age cuts ks schema) =
      cutsWord N (values cuts ks) (instantiate N C H p common schema) (a.eval C.age) := by
  induction ks with
  | nil =>
    change (schema.map (fun s => (s,()))).map
      (fun z => (instantiateStep N C H p common z.1,z.2)) =
      (schema.map (instantiateStep N C H p common)).map (fun op => (op,()))
    simp only [List.map_map]
    rfl
  | cons k ks ih =>
    exact (one_cut_agrees N C H p common (cuts k)
      (word_anchored C.age cuts ks schema a z ha)
      (word_ordered C.age cuts ks schema ho)).trans
      (congrArg (fun w => oneCutWord N (cuts k) w (a.eval C.age)) ih)

noncomputable def ranked {j : ℕ} (age : V → ℝ) (cuts : Fin j → ℚ)
    (ks : List (Fin j)) (schema : List (Step V E)) :
    List (Step V E × Fin ((values cuts ks).length+1)) :=
  (word age cuts ks schema).map (fun z => (z.1,rankTag (values cuts ks) z.2))

 theorem ranked_stable {j : ℕ} (cuts : Fin j → ℚ) (sig : Signature V j)
    {age age' : V → ℝ} (h : Realizes cuts sig age) (h' : Realizes cuts sig age')
    (ks : List (Fin j)) (schema : List (Step V E))
    (hs : ∀ a b, Step.interval a b ∈ schema → Available cuts a ∧ Available cuts b) :
    ranked age cuts ks schema = ranked age' cuts ks schema := by
  unfold ranked
  rw [word_stable cuts sig h h' ks schema hs]

 theorem ranked_agrees (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    {j : ℕ} (cuts : Fin j → ℚ) (ks : List (Fin j)) (schema : List (Step V E))
    (a z : AgeAtom V) (ha : Anchored a (schema.map (fun s => (s,()))) z)
    (ho : Ordered C.age (schema.map (fun s => (s,())))) :
    interpret N C H p common (ranked C.age cuts ks schema) =
      rankedWord N (values cuts ks) (instantiate N C H p common schema) (a.eval C.age) := by
  have h := congrArg (List.map (fun z => (z.1,rankTag (values cuts ks) z.2)))
    (word_agrees N C H p common cuts ks schema a z ha ho)
  simpa [ranked,rankedWord,interpret,List.map_map,Function.comp_def] using h

end UnifiedLean.G6.StableFiniteCutSchema
