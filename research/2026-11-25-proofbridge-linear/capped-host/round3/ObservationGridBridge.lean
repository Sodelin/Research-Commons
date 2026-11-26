import PresentedCappedHost

namespace ResearchCommons.AlexanderRouteB
open BirthOrder PopulationCounting PopulationReindex
open ResearchCommons.PresentedCappedHost
universe u v w

/-- A negative observation-fibre certificate needs a sound lift for every
admissible matching source, not merely one convenient representative. -/
theorem no_candidate_of_grid_lift {C : Type u} {A : Type v} {B : Type w}
    (admitted matching : C → Prop) (source : C → A → A → Option Nat)
    (host : B → B → Option Nat) (side : Nat)
    (hostNoGrid : ¬ HasGrid host side)
    (liftGrid : ∀ c, admitted c → matching c → HasGrid (source c) side)
    (liftEmbedding : ∀ c, admitted c → matching c → Embeds (source c) host) :
    ¬ ∃ c, admitted c ∧ matching c := by
  rintro ⟨c, hc, hm⟩
  exact hostNoGrid (embed_transports_grid (liftEmbedding c hc hm) (liftGrid c hc hm))

#print axioms no_candidate_of_grid_lift
end ResearchCommons.AlexanderRouteB
