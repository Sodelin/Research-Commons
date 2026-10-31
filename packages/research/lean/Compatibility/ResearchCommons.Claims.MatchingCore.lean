import GenericOrdinalCertificate
import GenericMortalRank
import BlowUpRankInvariance

/-! Frozen CB-ALEXANDER-003 exact source-specific classical formalization
interface, pending full-card review and NOT adopted. Original reachable
vertex/phase states and COMPLETE blow-up retained; terminal cloning is different.
The October2 novelty/eligibility correction remains authoritative. No new rank
theory, terminating infinite-input decision procedure or new novelty claim. -/
namespace ResearchCommons.Claims.MatchingCore
universe u v
variable {α : Type u} {V : Type u} {Label : Type v}

open GenericCertificate in
theorem well_founded_criterion (E : Graph V Label) (s : Nat → Label) :
    (¬ Realizes E s) ↔ WellFounded (Step E s) :=
  GenericCertificate.avoids_iff_wellFounded E s

open GenericCertificate GenericOrdinalCertificate in
theorem ordinal_criterion (E : Graph V Label) (s : Nat → Label) :
    (¬ Realizes E s) ↔
      ∃ rank : State E s → Ordinal.{u}, OrdinalCertificate E s rank :=
  GenericOrdinalCertificate.avoids_iff_ordinal_certificate E s

open GenericCertificate in
theorem natural_criterion (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) :
    (¬ Realizes E s) ↔ ∃ rank, NaturalCertificate E s rank :=
  GenericCertificate.avoids_iff_natural_certificate E s fin

open GenericCertificate GenericPruning in
theorem core_infinite_continuation (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) (x : State E s) :
    core (Step E s) x ↔ Live (Step E s) x :=
  GenericPruning.state_core_iff_infinite_continuation E s fin x

open GenericCertificate GenericPruning in
theorem core_greatest_fixed_point (E : Graph V Label)
    (s : Nat → Label) (fin : FiniteLabelChildren E) :
    derivative (Step E s) {x | core (Step E s) x} = {x | core (Step E s) x} ∧
      ∀ S, derivative (Step E s) S = S → S ⊆ {x | core (Step E s) x} :=
  GenericPruning.matching_core_is_greatest_fixed_point E s fin

open GenericCertificate GenericPruning GenericMortalRank in
theorem mortal_forward_closed (E : Graph V Label) (s : Nat → Label)
    {x y : State E s} (hx : ¬ core (Step E s) x) (hy : Step E s y x) :
    ¬ core (Step E s) y :=
  GenericMortalRank.mortal_forward_closed (Step E s) hx hy

open GenericCertificate GenericPruning GenericMortalRank in
theorem mortal_well_founded (E : Graph V Label) (s : Nat → Label) :
    WellFounded (GenericMortalRank.MortalStep (Step E s)) :=
  GenericMortalRank.mortal_wellFounded (Step E s)

open GenericCertificate GenericPruning GenericMortalRank in
theorem mortal_height_decreases (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) {x y : GenericMortalRank.Mortal (Step E s)}
    (hy : Step E s y.1 x.1) :
    GenericMortalRank.height (Step E s) (finite_state_children E s fin) y < GenericMortalRank.height (Step E s) (finite_state_children E s fin) x :=
  GenericMortalRank.height_decreases (Step E s) (finite_state_children E s fin) hy

open GenericCertificate GenericPruning GenericMortalRank in
theorem mortal_height_attained (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) (x : GenericMortalRank.Mortal (Step E s)) :
    survives (Step E s) (GenericMortalRank.height (Step E s) (finite_state_children E s fin) x) x.1 ∧
      ∀ n, survives (Step E s) n x.1 → n ≤ GenericMortalRank.height (Step E s) (finite_state_children E s fin) x :=
  GenericMortalRank.height_attained_and_bounds (Step E s) (finite_state_children E s fin) x

open GenericCertificate GenericPruning GenericMortalRank in
theorem mortal_height_least (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) (rank : GenericMortalRank.Mortal (Step E s) → Nat)
    (cert : ∀ {x y}, Step E s y.1 x.1 → rank y < rank x) :
    ∀ x, GenericMortalRank.height (Step E s) (finite_state_children E s fin) x ≤ rank x :=
  GenericMortalRank.height_least (Step E s) (finite_state_children E s fin) rank cert

open GenericCertificate GenericPruning GenericMortalRank in
theorem mortal_exact_survival (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) (x : GenericMortalRank.Mortal (Step E s)) (n : Nat) :
    survives (Step E s) n x.1 ↔ n ≤ GenericMortalRank.height (Step E s) (finite_state_children E s fin) x :=
  GenericMortalRank.survives_iff_le_height (Step E s) (finite_state_children E s fin) x n

open GenericCertificate GenericPruning GenericMortalRank in
theorem matching_state_dichotomy (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) (x : State E s) :
    Live (Step E s) x ∨ ∃ h : Nat, survives (Step E s) h x ∧
      ∀ n, survives (Step E s) n x → n ≤ h :=
  GenericMortalRank.matching_state_dichotomy E s fin x

open GenericCertificate GenericPruning in
theorem phase_zero_realization (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) (vertex : V) :
    core (Step E s) (startState E s vertex) ↔
      ∃ p : Nat → V, p 0 = vertex ∧ ∀ n, E (p n) (p (n+1)) (s n) :=
  GenericPruning.start_core_iff_realizes_from E s fin vertex

open GenericCertificate GenericUniversalAvoiders in
theorem complete_blowup_reachability (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label) (x : Fibre V m) (k : Nat) :
    Reachable (liftedEdge p m) s x k ↔ Reachable p.edge s x.1 k :=
  BlowUpRankInvariance.reachable_iff p m hm s x k

open GenericCertificate GenericUniversalAvoiders BlowUpRankInvariance in
theorem complete_blowup_finite_lengths (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label)
    (x : State (liftedEdge p m) s) (n : Nat) :
    ChainLength (Step (liftedEdge p m) s) x n ↔
      ChainLength (Step p.edge s) (projectState p m hm s x) n :=
  BlowUpRankInvariance.chainLength_iff p m hm s x n

open GenericCertificate GenericUniversalAvoiders BlowUpRankInvariance in
theorem complete_blowup_height (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label)
    (finP : ∀ x : State p.edge s, Finite {y // Step p.edge s y x})
    (wfP : WellFounded (Step p.edge s))
    (finQ : ∀ x : State (liftedEdge p m) s, Finite {y // Step (liftedEdge p m) s y x})
    (wfQ : WellFounded (Step (liftedEdge p m) s))
    (x : State (liftedEdge p m) s) :
    finiteHeight (Step (liftedEdge p m) s) finQ wfQ x =
      finiteHeight (Step p.edge s) finP wfP (projectState p m hm s x) :=
  BlowUpRankInvariance.finiteHeight_eq p m hm s finP wfP finQ wfQ x

open GenericCertificate GenericUniversalAvoiders BlowUpRankInvariance in
theorem actual_population_rank_transport (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label)
    (avoid : ¬ GenericCertificate.Realizes p.edge s) :
    ∃ r : State p.edge s → Nat,
      NaturalCertificate p.edge s r ∧
      (∀ other, NaturalCertificate p.edge s other → ∀ x, r x ≤ other x) ∧
      (∀ x, ChainLength (Step p.edge s) x (r x)) ∧
      NaturalCertificate (liftedEdge p m) s (fun x => r (projectState p m hm s x)) ∧
      (∀ other, NaturalCertificate (liftedEdge p m) s other →
        ∀ x, r (projectState p m hm s x) ≤ other x) ∧
      (∀ x, ChainLength (Step (liftedEdge p m) s) x (r (projectState p m hm s x))) :=
  BlowUpRankInvariance.avoider_has_exact_rank_transport p m hm s avoid

end ResearchCommons.Claims.MatchingCore
