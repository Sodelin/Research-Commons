import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! The OLD coherent finite parameter filter, expressed on its actual arrays.
One map at an epoch is used on BOTH adjacent routing layers. These finite
equations do not construct a genealogy source or prove their observability.
The complete canonical-history classification remains a separate join. -/
namespace ResearchCommons.MSCI.Alignment
set_option autoImplicit false

variable (J : ℕ) (count : Fin (J+1) → ℕ)

/-- Exactly the supplied durations, rate vectors and routing matrices, after
the OLD preliminary alignment has fixed the common epoch/count shape. -/
structure Parameters where
  duration : Fin J → ℚ
  rate : (j : Fin (J+1)) → Fin (count j) → ℚ
  routing : (j : Fin J) → Fin (count j.castSucc) → Fin (count j.succ) → ℚ

/-- Finite maps first; bijectivity is checked, rather than presumed for a
native integer table. This also makes the entire result independently finite. -/
abbrev Rename := (j : Fin (J+1)) → Fin (count j) → Fin (count j)

def Matches (F G : Parameters J count) (σ : Rename J count) : Prop :=
  (∀ j, Function.Bijective (σ j)) ∧
  (∀ i, σ 0 i = i) ∧
  (∀ i, σ (Fin.last J) i = i) ∧
  (∀ j, F.duration j = G.duration j) ∧
  (∀ j i, F.rate j i = G.rate j (σ j i)) ∧
  (∀ j i k, F.routing j i k =
    G.routing j (σ j.castSucc i) (σ j.succ k))

instance matchesDecidable (F G : Parameters J count) (σ : Rename J count) :
    Decidable (Matches J count F G σ) := by
  unfold Matches
  infer_instance

/-- This finite mathematical filter is a receiver, not a second native
search implementation or a biological admission factory. -/
def allAlignments (F G : Parameters J count) : Finset (Rename J count) :=
  Finset.univ.filter (Matches J count F G)

theorem mem_allAlignments_iff (F G : Parameters J count) (σ : Rename J count) :
    σ ∈ allAlignments J count F G ↔ Matches J count F G σ := by
  simp [allAlignments]

theorem allAlignments_nonempty_iff (F G : Parameters J count) :
    (allAlignments J count F G).Nonempty ↔ ∃ σ, Matches J count F G σ := by
  simp only [Finset.Nonempty, mem_allAlignments_iff]

theorem matches_refl (F : Parameters J count) :
    Matches J count F F (fun _ i => i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact Function.bijective_id
  · intro i; rfl
  · intro i; rfl
  · intro j; rfl
  · intro j i; rfl
  · intro j i k; rfl

/-- Combining legal renamings retains the SAME intermediate coordinate on
both sides of every boundary. No independent layerwise permutation occurs. -/
theorem matches_trans (F G H : Parameters J count) (σ τ : Rename J count)
    (hFG : Matches J count F G σ) (hGH : Matches J count G H τ) :
    Matches J count F H (fun j i => τ j (σ j i)) := by
  rcases hFG with ⟨hs, h0, hlast, hd, hr, hb⟩
  rcases hGH with ⟨ht, ht0, htlast, htd, htr, htb⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (ht j).comp (hs j)
  · intro i
    rw [h0, ht0]
  · intro i
    rw [hlast, htlast]
  · intro j
    exact (hd j).trans (htd j)
  · intro j i
    exact (hr j i).trans (htr j (σ j i))
  · intro j i k
    exact (hb j i k).trans (htb j (σ j.castSucc i) (σ j.succ k))

end ResearchCommons.MSCI.Alignment
