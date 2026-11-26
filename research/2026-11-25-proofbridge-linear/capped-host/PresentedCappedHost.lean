import SamuelAlexanderResearch.PopulationReindex
import CappedGridObstruction

/-! Consume the grid obstruction in the original host vertex/time types.
No enumeration or natural-order embedding is an input to this consumer. -/

namespace ResearchCommons.PresentedCappedHost
open PopulationCounting PopulationReindex
open ResearchCommons.CappedConnectedBags ResearchCommons.CappedGridObstruction

universe u v w x
variable {V : Type u} {Time : Type v} [LE Time] [LT Time]
  [Std.IsLinearPreorder Time] [Std.LawfulOrderLT Time]
  {birth : V → Time} {k : Nat}

/-- A full grid is not needed: any injective cell map preserving the horizontal
and vertical edges (with either orientation) suffices. -/
def HasGrid (edge : V → V → Option Nat) (side : Nat) : Prop :=
  ∃ f : Fin side × Fin side → V,
    (∀ x y, f x = f y → x = y) ∧
    (∀ a b : Fin side × Fin side,
      (a.1 = b.1 ∧ a.2.val + 1 = b.2.val) ∨
      (a.1.val + 1 = b.1.val ∧ a.2 = b.2) →
        (edge (f a) (f b)).isSome = true ∨ (edge (f b) (f a)).isSome = true)

theorem no_large_presented_grid (p : PresentedPopulation birth k k) (side : Nat)
    (large : k * fullRootCount (toNatPopulation p) + 1 < side)
    (grid : HasGrid p.edge side) : False := by
  let e := enumeration p
  obtain ⟨f, hinj, hadj⟩ := grid
  let F (r c : Nat) : Nat :=
    if h : r < side ∧ c < side then e.index (f (⟨r,h.1⟩,⟨c,h.2⟩)) else 0
  have hf (r c : Fin side) : F r.val c.val = e.index (f (r,c)) := by
    simp [F, r.isLt, c.isLt]
  have transport (a b : Fin side × Fin side)
      (hab : (a.1 = b.1 ∧ a.2.val + 1 = b.2.val) ∨
             (a.1.val + 1 = b.1.val ∧ a.2 = b.2)) :
      Adj (toNatPopulation p) (F a.1.val a.2.val) (F b.1.val b.2.val) := by
    simpa only [hf, Adj, toNatPopulation_edge, e, BirthOrder.OrderedEnumeration.toFun_index]
      using hadj a b hab
  apply no_large_grid (toNatPopulation p) side large F
  · intro r c hr hc
    exact transport (⟨r,hr⟩,⟨c,by omega⟩) (⟨r,hr⟩,⟨c+1,hc⟩) (Or.inl ⟨rfl,rfl⟩)
  · intro r c hr hc
    exact transport (⟨r,by omega⟩,⟨c,hc⟩) (⟨r+1,hr⟩,⟨c,hc⟩) (Or.inr ⟨rfl,rfl⟩)
  · intro ⟨r,c⟩ ⟨s,d⟩ ⟨hr,hc⟩ ⟨hs,hd⟩ h
    have hi : e.index (f (⟨r,hr⟩,⟨c,hc⟩)) = e.index (f (⟨s,hs⟩,⟨d,hd⟩)) := by
      exact (hf ⟨r,hr⟩ ⟨c,hc⟩).symm.trans (h.trans (hf ⟨s,hs⟩ ⟨d,hd⟩))
    have heq := congrArg e.toFun hi
    rw [e.toFun_index,e.toFun_index] at heq
    exact congrArg (fun z : Fin side × Fin side => (z.1.val,z.2.val)) (hinj _ _ heq)

/-- A minimal graph embedding: injectivity and preservation of undirected
adjacency only. The source and host may use unrelated directions and labels. -/
def Embeds {A : Type w} {B : Type x}
    (source : A → A → Option Nat) (host : B → B → Option Nat) : Prop :=
  ∃ g : A → B, (∀ a b, g a = g b → a = b) ∧
    ∀ a b, ((source a b).isSome = true ∨ (source b a).isSome = true) →
      (host (g a) (g b)).isSome = true ∨ (host (g b) (g a)).isSome = true

theorem embed_transports_grid {A : Type w}
    {source : A → A → Option Nat} {host : V → V → Option Nat} {side : Nat}
    (emb : Embeds source host) (grid : HasGrid source side) : HasGrid host side := by
  obtain ⟨g, g_inj, preserves⟩ := emb
  obtain ⟨f, f_inj, edges⟩ := grid
  exact ⟨fun a => g (f a), fun a b eq => f_inj a b (g_inj _ _ eq),
    fun a b e => preserves _ _ (edges a b e)⟩

/-- An actual capped host cannot embed a source containing a grid above its
explicit root budget, even with undirected adjacency alone. -/
theorem no_presented_grid_source_embedding (p : PresentedPopulation birth k k)
    {A : Type w} {source : A → A → Option Nat} {side : Nat}
    (large : k * fullRootCount (toNatPopulation p) + 1 < side)
    (grid : HasGrid source side) : ¬ Embeds source p.edge :=
  fun embed => no_large_presented_grid p side large (embed_transports_grid embed grid)

/-- A listed cover of real roots gives a usable bound without computing
the noncomputable chronology or exact root count. -/
theorem root_count_le_original_cover (p : PresentedPopulation birth k k)
    (roots : List V) (cover : ∀ x, NoParents p.edge x → x ∈ roots) :
    fullRootCount (toNatPopulation p) ≤ roots.length := by
  have bound := sumBelow_indicator_le_cover (indexedRoot p) (rootSupport p)
    (roots.map (enumeration p).index) (by
      intro i _ hi
      exact (enumeration p).pullback_cover (NoParents p.edge) roots cover i
        ((indexedRoot_true_iff p i).mp hi))
  change sumBelow (rootSupport p) (fun i => if indexedRoot p i then 1 else 0) ≤ roots.length
  simpa only [List.length_map] using bound

/-- Choose an explicit grid side from any original root cover. This removes
dependence of the counterexample's size on the abstract enumeration. -/
theorem misses_source_at_cover_size (p : PresentedPopulation birth k k)
    (roots : List V) (cover : ∀ x, NoParents p.edge x → x ∈ roots)
    {A : Type w} {source : A → A → Option Nat}
    (grid : HasGrid source (k * roots.length + 2)) : ¬ Embeds source p.edge := by
  apply no_presented_grid_source_embedding p _ grid
  have h := Nat.mul_le_mul_left k (root_count_le_original_cover p roots cover)
  omega

/-- Form of the full host reduction: give a cofinal supply of *eligible*
sources with grids, and every capped presented host has a missing source.
The eligible-source provider is deliberately an explicit remaining input. -/
theorem misses_eligible_source
    {A : Nat → Type w} (source : (n : Nat) → A n → A n → Option Nat)
    (eligible : Nat → Prop)
    (cofinal : ∀ b : Nat, ∃ n, b < n ∧ eligible n ∧ HasGrid (source n) n)
    (p : PresentedPopulation birth k k) :
    ∃ n, eligible n ∧ ¬ Embeds (source n) p.edge := by
  obtain ⟨n, hn, hE, hG⟩ := cofinal (k * fullRootCount (toNatPopulation p) + 1)
  exact ⟨n,hE,no_presented_grid_source_embedding p hn hG⟩

end ResearchCommons.PresentedCappedHost

#print axioms ResearchCommons.PresentedCappedHost.misses_eligible_source

#print axioms ResearchCommons.PresentedCappedHost.misses_source_at_cover_size
