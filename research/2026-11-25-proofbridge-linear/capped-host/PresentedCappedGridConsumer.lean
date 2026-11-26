import PresentedCappedHost
import CappedPresentedPadding
import FixedGender

namespace ResearchCommons.PresentedCappedHost
open ResearchCommons.CappedPaddingLanguage ResearchCommons.CappedLabeledGrid
open PopulationReindex CappedPresentedPadding

theorem right_summand_keeps_grid {V W : Type}
    (base : V → V → Option Nat) (pad : W → W → Option Nat)
    {side : Nat} (grid : HasGrid pad side) : HasGrid (joined base pad) side :=
  embed_transports_grid ⟨Sum.inr, fun _ _ h => Sum.inr.inj h, fun _ _ h => h⟩ grid

theorem attached_pad_keeps_grid {V W Time : Type} [LE Time] [LT Time]
    {birth : V → Time} {k d side : Nat} (p : PresentedPopulation birth k d)
    (q : FinitePad W Time k d) (grid : HasGrid q.edge side) :
    HasGrid (attach p q).edge side :=
  right_summand_keeps_grid p.edge q.edge grid

theorem fixed_gender_grid_has_grid (side k : Nat) : HasGrid (@FixedGender.fixedEdge side k) side := by
  refine ⟨Sum.inr, fun _ _ h => Sum.inr.inj h, ?_⟩
  intro a b h
  left
  rw [FixedGender.grid_edge a b h]
  rfl

end ResearchCommons.PresentedCappedHost
#print axioms ResearchCommons.PresentedCappedHost.attached_pad_keeps_grid
#print axioms ResearchCommons.PresentedCappedHost.fixed_gender_grid_has_grid
