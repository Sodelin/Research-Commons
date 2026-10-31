import RealSpeciesTheorem

/-! Candidate only, not compiled. Generic-carrier wrapper of the accepted
Nat-carrier founder-window theorem. Adapted from SpeciesReindex at public pin
e2502c82ab9a77c00543932f775a71e5374221f7; all prior attribution preserved.
The native source predicates below are defined directly on V, not by assuming
the desired transported conclusion. No graph, chronological date or competitor
is discarded. -/
namespace FounderCarrier
open SpeciesBridge FounderWindowResearch BirthOrder
universe u
variable {V : Type u}

inductive VDescendant (E : V → V → Prop) : V → V → Prop where
  | edge {a b} : E a b → VDescendant E a b
  | snoc {a b c} : VDescendant E a b → E b c → VDescendant E a c

inductive VWeakReach (E : V → V → Prop) (S : V → Prop) : V → V → Prop where
  | refl {a} : S a → VWeakReach E S a a
  | edge {a b} : S a → S b → (E a b ∨ E b a) → VWeakReach E S a b
  | trans {a b c} : VWeakReach E S a b → VWeakReach E S b c → VWeakReach E S a c

def VWeaklyConnected (E : V → V → Prop) (S : V → Prop) : Prop :=
  (∃ a, S a) ∧ ∀ a b, S a → S b → VWeakReach E S a b

def VIAP (E : V → V → Prop) (S : V → Prop) : Prop :=
  ∀ a, S a → BirthOrder.FiniteCover (fun b => S b ∧ VDescendant E a b) ∨
    BirthOrder.FiniteCover (fun b => S b ∧ ¬ VDescendant E a b)

def VConvex (E : V → V → Prop) (S : V → Prop) : Prop :=
  ∀ b, (∃ a, S a ∧ VDescendant E a b) →
    (∃ c, S c ∧ VDescendant E b c) → S b

def VReflection (E : V → V → Prop) (S : V → Prop) : Prop :=
  ∀ a, S a → (¬ BirthOrder.FiniteCover (VDescendant E a)) →
    ¬ BirthOrder.FiniteCover (fun b => S b ∧ VDescendant E a b)

def VCommonAncestor (E : V → V → Prop) (S : V → Prop) : Prop :=
  ∃ a, S a ∧ ∀ b, S b → b ≠ a → VDescendant E a b

def VSpecieslike (E : V → V → Prop) (S : V → Prop) : Prop :=
  VWeaklyConnected E S ∧ VIAP E S ∧ VConvex E S

def VFounder (E : V → V → Prop) (S : V → Prop) (a : V) : Prop :=
  S a ∧ ∀ b, S b → ¬ VDescendant E b a

def VWindow (E : V → V → Prop) (birth : V → ℝ) (duration : ℝ)
    (S : V → Prop) : Prop :=
  ∃ start, S start ∧ (∀ a, S a → birth start ≤ birth a) ∧
    ∀ r, VFounder E S r → birth r ≤ birth start + duration

def VWindowSpecies (E : V → V → Prop) (birth : V → ℝ) (duration : ℝ)
    (S : V → Prop) : Prop :=
  VSpecieslike E S ∧ VReflection E S ∧ VWindow E birth duration S

def VMaximalWindowSpecies (E : V → V → Prop) (birth : V → ℝ)
    (duration : ℝ) (S : V → Prop) : Prop :=
  VWindowSpecies E birth duration S ∧
    ∀ T, (∀ a, S a → T a) → VWindowSpecies E birth duration T → ∀ a, T a → S a

noncomputable section
variable {birth : V → ℝ}

def pullGraph (e : OrderedEnumeration birth) (E : V → V → Prop) : Graph :=
  fun i j => E (e.toFun i) (e.toFun j)
def pullSet (e : OrderedEnumeration birth) (S : V → Prop) : NatSet :=
  fun i => S (e.toFun i)
def pushSet (e : OrderedEnumeration birth) (T : NatSet) : V → Prop :=
  fun a => T (e.index a)
def pulledBirth (e : OrderedEnumeration birth) : Nat → ℝ :=
  fun i => birth (e.toFun i)
variable (e : OrderedEnumeration birth)

theorem pull_push (T : NatSet) : pullSet e (pushSet e T) = T := by
  funext i
  exact congrArg T (e.index_toFun i)

theorem descendant_map {E : V → V → Prop} {i j : Nat} (h : Descendant (pullGraph e E) i j) :
    VDescendant E (e.toFun i) (e.toFun j) := by
  induction h with
  | edge he => exact .edge he
  | snoc _ he ih => exact .snoc ih he

theorem descendant_index {E : V → V → Prop} {a b : V} (h : VDescendant E a b) :
    Descendant (pullGraph e E) (e.index a) (e.index b) := by
  induction h with
  | edge he =>
    exact .edge (by simpa only [pullGraph, e.toFun_index] using he)
  | snoc _ he ih =>
    exact .snoc ih (by simpa only [pullGraph, e.toFun_index] using he)

theorem descendant_iff (E : V → V → Prop) (i j : Nat) :
    Descendant (pullGraph e E) i j ↔ VDescendant E (e.toFun i) (e.toFun j) := by
  constructor
  · exact descendant_map e
  · intro h
    simpa only [e.index_toFun] using descendant_index e h

theorem finiteSupport_iff (S : V → Prop) :
    FiniteSupport (pullSet e S) ↔ BirthOrder.FiniteCover S :=
  e.finiteCover_pullback_iff S

theorem infiniteSupport_iff (S : V → Prop) :
    InfiniteSupport (pullSet e S) ↔ (¬ BirthOrder.FiniteCover S) :=
  not_congr (finiteSupport_iff e S)

private theorem finiteSupport_congr {S T : NatSet} (h : ∀ v, S v ↔ T v) :
    FiniteSupport S ↔ FiniteSupport T :=
  ⟨fun hs => finiteSupport_mono (fun v hv => (h v).mpr hv) hs,
   fun ht => finiteSupport_mono (fun v hv => (h v).mp hv) ht⟩

theorem finite_descendants_iff (E : V → V → Prop) (S : V → Prop) (i : Nat) :
    FiniteSupport (fun j => pullSet e S j ∧ Descendant (pullGraph e E) i j) ↔
      BirthOrder.FiniteCover (fun v => S v ∧ VDescendant E (e.toFun i) v) :=
  (finiteSupport_congr (fun j => and_congr Iff.rfl (descendant_iff e E i j))).trans
    (finiteSupport_iff e (fun v => S v ∧ VDescendant E (e.toFun i) v))

theorem finite_nondescendants_iff (E : V → V → Prop) (S : V → Prop) (i : Nat) :
    FiniteSupport (fun j => pullSet e S j ∧ ¬ Descendant (pullGraph e E) i j) ↔
      BirthOrder.FiniteCover (fun v => S v ∧ ¬ VDescendant E (e.toFun i) v) :=
  (finiteSupport_congr (fun j => and_congr Iff.rfl (not_congr (descendant_iff e E i j)))).trans
    (finiteSupport_iff e (fun v => S v ∧ ¬ VDescendant E (e.toFun i) v))

theorem infinite_descendants_iff (E : V → V → Prop) (i : Nat) :
    InfiniteSupport (Descendant (pullGraph e E) i) ↔
      (¬ BirthOrder.FiniteCover (VDescendant E (e.toFun i))) :=
  not_congr ((finiteSupport_congr (fun j => descendant_iff e E i j)).trans
    (finiteSupport_iff e (VDescendant E (e.toFun i))))

theorem iap_iff (E : V → V → Prop) (S : V → Prop) :
    IAP (pullGraph e E) (pullSet e S) ↔ VIAP E S := by
  constructor
  · intro h v hv
    obtain ⟨i, rfl⟩ := e.surjective v
    rcases h i hv with hpos | hneg
    · exact Or.inl ((finite_descendants_iff e E S i).mp hpos)
    · exact Or.inr ((finite_nondescendants_iff e E S i).mp hneg)
  · intro h i hi
    rcases h (e.toFun i) hi with hpos | hneg
    · exact Or.inl ((finite_descendants_iff e E S i).mpr hpos)
    · exact Or.inr ((finite_nondescendants_iff e E S i).mpr hneg)

theorem convex_iff (E : V → V → Prop) (S : V → Prop) :
    Convex (pullGraph e E) (pullSet e S) ↔ VConvex E S := by
  constructor
  · intro h v ha hd
    obtain ⟨a, ha, hav⟩ := ha
    obtain ⟨d, hd, hvd⟩ := hd
    have hm := h (e.index v)
      ⟨e.index a, by simpa only [pullSet, e.toFun_index] using ha, descendant_index e hav⟩
      ⟨e.index d, by simpa only [pullSet, e.toFun_index] using hd, descendant_index e hvd⟩
    simpa only [pullSet, e.toFun_index] using hm
  · intro h i ha hd
    obtain ⟨a, ha, hai⟩ := ha
    obtain ⟨d, hd, hid⟩ := hd
    exact h (e.toFun i) ⟨e.toFun a, ha, descendant_map e hai⟩
      ⟨e.toFun d, hd, descendant_map e hid⟩

theorem reflection_iff (E : V → V → Prop) (S : V → Prop) :
    Reflection (pullGraph e E) (pullSet e S) ↔ VReflection E S := by
  constructor
  · intro h v hv hinf
    obtain ⟨i, rfl⟩ := e.surjective v
    have hi := h i hv ((infinite_descendants_iff e E i).mpr hinf)
    exact (not_congr (finite_descendants_iff e E S i)).mp hi
  · intro h i hi hinf
    have hv := h (e.toFun i) hi ((infinite_descendants_iff e E i).mp hinf)
    exact (not_congr (finite_descendants_iff e E S i)).mpr hv

theorem weakReach_map {E : V → V → Prop} {S : V → Prop} {i j : Nat}
    (h : WeakReach (pullGraph e E) (pullSet e S) i j) :
    VWeakReach E S (e.toFun i) (e.toFun j) := by
  induction h with
  | refl hi => exact .refl hi
  | edge hi hj he => exact .edge hi hj he
  | trans _ _ ih ij => exact .trans ih ij

theorem weakReach_index {E : V → V → Prop} {S : V → Prop} {a b : V}
    (h : VWeakReach E S a b) :
    WeakReach (pullGraph e E) (pullSet e S) (e.index a) (e.index b) := by
  induction h with
  | refl ha => exact .refl (by simpa only [pullSet, e.toFun_index] using ha)
  | edge ha hb he =>
    exact .edge (by simpa only [pullSet, e.toFun_index] using ha)
      (by simpa only [pullSet, e.toFun_index] using hb)
      (by simpa only [pullGraph, e.toFun_index] using he)
  | trans _ _ ih ij => exact .trans ih ij

theorem weakReach_iff (E : V → V → Prop) (S : V → Prop) (i j : Nat) :
    WeakReach (pullGraph e E) (pullSet e S) i j ↔
      VWeakReach E S (e.toFun i) (e.toFun j) := by
  constructor
  · exact weakReach_map e
  · intro h
    simpa only [e.index_toFun] using weakReach_index e h

theorem weaklyConnected_iff (E : V → V → Prop) (S : V → Prop) :
    WeaklyConnected (pullGraph e E) (pullSet e S) ↔ VWeaklyConnected E S := by
  constructor
  · rintro ⟨⟨i, hi⟩, paths⟩
    refine ⟨⟨e.toFun i, hi⟩, ?_⟩
    intro a b ha hb
    obtain ⟨i, rfl⟩ := e.surjective a
    obtain ⟨j, rfl⟩ := e.surjective b
    exact weakReach_map e (paths i j ha hb)
  · rintro ⟨⟨a, ha⟩, paths⟩
    obtain ⟨i, rfl⟩ := e.surjective a
    refine ⟨⟨i, ha⟩, ?_⟩
    intro j k hj hk
    exact (weakReach_iff e E S j k).mpr (paths _ _ hj hk)

theorem commonAncestor_iff (E : V → V → Prop) (S : V → Prop) :
    CommonAncestor (pullGraph e E) (pullSet e S) ↔ VCommonAncestor E S := by
  constructor
  · rintro ⟨i, hi, paths⟩
    refine ⟨e.toFun i, hi, ?_⟩
    intro v hv hne
    obtain ⟨j, rfl⟩ := e.surjective v
    exact (descendant_iff e E i j).mp
      (paths j hv (fun heq => hne (congrArg e.toFun heq)))
  · rintro ⟨a, ha, paths⟩
    obtain ⟨i, rfl⟩ := e.surjective a
    refine ⟨i, ha, ?_⟩
    intro j hj hne
    exact (descendant_iff e E i j).mpr
      (paths _ hj (fun heq => hne (e.injective j i heq)))

theorem founder_iff (E : V → V → Prop) (S : V → Prop) (i : Nat) :
    Founder (pullGraph e E) (pullSet e S) i ↔ VFounder E S (e.toFun i) := by
  constructor
  · rintro ⟨hi, noAncestor⟩
    refine ⟨hi, ?_⟩
    intro a ha hai
    obtain ⟨j, rfl⟩ := e.surjective a
    exact noAncestor j ha ((descendant_iff e E j i).mpr hai)
  · rintro ⟨hi, noAncestor⟩
    exact ⟨hi, fun j hj hji => noAncestor _ hj ((descendant_iff e E j i).mp hji)⟩

theorem finite_founders_iff (E : V → V → Prop) (S : V → Prop) :
    FiniteSupport (Founder (pullGraph e E) (pullSet e S)) ↔
      BirthOrder.FiniteCover (VFounder E S) :=
  (finiteSupport_congr (fun i => founder_iff e E S i)).trans
    (finiteSupport_iff e (VFounder E S))

/-- The identical real duration is preserved; birth times are composed with the bijection. -/
theorem window_iff (E : V → V → Prop) (S : V → Prop) (duration : ℝ) :
    RealFounderWindow.Window (pullGraph e E) (pulledBirth e) duration (pullSet e S) ↔
      VWindow E birth duration S := by
  constructor
  · rintro ⟨i, hi, earliest, bound⟩
    refine ⟨e.toFun i, hi, ?_, ?_⟩
    · intro v hv
      obtain ⟨j, rfl⟩ := e.surjective v
      exact earliest j hv
    · intro r hr
      obtain ⟨j, rfl⟩ := e.surjective r
      exact bound j ((founder_iff e E S j).mpr hr)
  · rintro ⟨a, ha, earliest, bound⟩
    obtain ⟨i, rfl⟩ := e.surjective a
    refine ⟨i, ha, ?_, ?_⟩
    · intro j hj
      exact earliest _ hj
    · intro j hj
      exact bound _ ((founder_iff e E S j).mp hj)

theorem specieslike_iff (E : V → V → Prop) (S : V → Prop) :
    Specieslike (pullGraph e E) (pullSet e S) ↔ VSpecieslike E S :=
  and_congr (weaklyConnected_iff e E S)
    (and_congr (iap_iff e E S) (convex_iff e E S))


theorem windowSpecies_iff (E : V → V → Prop) (S : V → Prop) (duration : ℝ) :
    FounderMaximal.WindowSpecies (pullGraph e E) (pulledBirth e) duration (pullSet e S) ↔
      VWindowSpecies E birth duration S :=
  and_congr (specieslike_iff e E S)
    (and_congr (reflection_iff e E S) (window_iff e E S duration))

theorem push_maximal (E : V → V → Prop) (duration : ℝ) (T : NatSet)
    (hT : FounderMaximal.MaximalWindowSpecies
      (pullGraph e E) (pulledBirth e) duration T) :
    VMaximalWindowSpecies E birth duration (pushSet e T) := by
  refine ⟨(windowSpecies_iff e E (pushSet e T) duration).mp ?_, ?_⟩
  · simpa only [pull_push] using hT.1
  · intro U hTU hU a ha
    have hinc : ∀ i, T i → pullSet e U i := by
      intro i hi
      apply hTU (e.toFun i)
      simpa only [pushSet, e.index_toFun] using hi
    have hback := hT.2 (pullSet e U) hinc ((windowSpecies_iff e E U duration).mpr hU)
    exact hback (e.index a) (by simpa only [pullSet, e.toFun_index] using ha)

def actualEnumeration (birth : V → ℝ) (infinite : BirthOrder.InfiniteVertices V)
    (finite : ∀ t : ℝ, BirthOrder.FiniteCover (fun a => birth a < t)) :
    OrderedEnumeration birth :=
  BirthOrder.orderedEnumeration birth infinite (by
    intro t
    obtain ⟨xs, hxs⟩ := finite (t + 1)
    exact ⟨xs, fun a ha => hxs a (by linarith)⟩)

theorem maximal_window_extension (E : V → V → Prop) (birth : V → ℝ)
    (infinite : BirthOrder.InfiniteVertices V)
    (finite : ∀ t : ℝ, BirthOrder.FiniteCover (fun a => birth a < t))
    (chronological : ∀ a b, E a b → birth a < birth b)
    (children : ∀ a, BirthOrder.FiniteCover (E a))
    (duration : ℝ) (S : V → Prop) (hS : VWindowSpecies E birth duration S) :
    ∃ M, (∀ a, S a → M a) ∧ VMaximalWindowSpecies E birth duration M := by
  let e := actualEnumeration birth infinite finite
  have hf : RealFounderWindow.StrictFiniteSublevels (pulledBirth e) :=
    fun t => (finiteSupport_iff e (fun a => birth a < t)).mpr (finite t)
  have hc : RealFounderWindow.Chronological (pullGraph e E) (pulledBirth e) :=
    fun i j he => chronological _ _ he
  have hchild : ∀ i, FiniteSupport (pullGraph e E i) :=
    fun i => (finiteSupport_iff e (E (e.toFun i))).mpr (children _)
  obtain ⟨T, hST, hT⟩ := RealSpeciesTheorem.maximal_window_extension
    (pullGraph e E) (pulledBirth e) hf hc hchild duration (pullSet e S)
    ((windowSpecies_iff e E S duration).mpr hS)
  refine ⟨pushSet e T, ?_, push_maximal e E duration T hT⟩
  intro a ha
  exact hST (e.index a) (by simpa only [pullSet, e.toFun_index] using ha)

theorem every_vertex_in_maximal_real_window (E : V → V → Prop) (birth : V → ℝ)
    (infinite : BirthOrder.InfiniteVertices V)
    (finite : ∀ t : ℝ, BirthOrder.FiniteCover (fun a => birth a < t))
    (chronological : ∀ a b, E a b → birth a < birth b)
    (children : ∀ a, BirthOrder.FiniteCover (E a))
    (duration : ℝ) (nonnegative : 0 ≤ duration) (a : V) :
    ∃ M, M a ∧ VMaximalWindowSpecies E birth duration M := by
  let e := actualEnumeration birth infinite finite
  have hf : RealFounderWindow.StrictFiniteSublevels (pulledBirth e) :=
    fun t => (finiteSupport_iff e (fun a => birth a < t)).mpr (finite t)
  have hc : RealFounderWindow.Chronological (pullGraph e E) (pulledBirth e) :=
    fun i j he => chronological _ _ he
  have hchild : ∀ i, FiniteSupport (pullGraph e E i) :=
    fun i => (finiteSupport_iff e (E (e.toFun i))).mpr (children _)
  obtain ⟨T, ha, hT⟩ := RealSpeciesTheorem.every_vertex_in_maximal_real_window
    (pullGraph e E) (pulledBirth e) hf hc hchild duration nonnegative (e.index a)
  exact ⟨pushSet e T, ha, push_maximal e E duration T hT⟩

end
end FounderCarrier
#print axioms FounderCarrier.descendant_iff
#print axioms FounderCarrier.windowSpecies_iff
#print axioms FounderCarrier.push_maximal
#print axioms FounderCarrier.every_vertex_in_maximal_real_window

#print axioms FounderCarrier.maximal_window_extension
