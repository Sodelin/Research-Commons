import StatefulCAReal

/-! Existing CB-POPULATION-004 owner/type correspondence, pending review.
Original synthetic rule, full real hulls and global evolution proofs are retained.
The only finite-support join below unfolds the already specified lDomino.
No published or binary Life-like rule, native simulator or novelty claim. -/
namespace ResearchCommons.Claims.StatefulCertificates
open StatefulCA

theorem actual_static_certificate : FixedCert Aligned Diagonal :=
  aligned_diagonal_certificate

theorem full_real_static_support (a b : Dir → Prop) (cert : FixedCert a b) :
    IsGreatest ((fun v : ℝ × ℝ => v.1) ''
      (StatefulCAReal.hull a ∩ StatefulCAReal.hull b)) 1 :=
  StatefulCAReal.static_east_support_one a b cert

theorem actual_global_charge_strip (c : Config) (lo hi : Int)
    (bound : ChargeBound c lo hi) (n : Nat) :
    ChargeBound (iterate c n) lo hi :=
  all_generations_in_initial_charge_strip c lo hi bound n

theorem no_horizontal_translation (c : Config) (period : Nat) (dx dy : Int)
    (finite : FiniteSupport c) (nonempty : ∃ x y, c x y ≠ dead)
    (recurs : iterate c period = translate c dx dy) : dx = 0 :=
  no_horizontal_spaceship c period dx dy finite nonempty recurs

/-- Physical velocity is interpreted at positive period; the original real
quotient theorem is retained also at the totalized zero-period input. -/
theorem horizontal_velocity_zero (c : Config) (period : Nat) (dx dy : Int)
    (finite : FiniteSupport c) (nonempty : ∃ x y, c x y ≠ dead)
    (recurs : iterate c period = translate c dx dy) :
    (dx : ℝ) / (period : ℝ) = 0 :=
  StatefulCAReal.real_horizontal_spaceship_speed_zero c period dx dy finite nonempty recurs

/-- Both full configurations include the dead exterior; this is a genuine
finite nonempty two-cycle of the same evolve function, not a checked crop. -/
theorem finite_nontrivial_oscillator :
    FiniteSupport rDomino ∧ FiniteSupport lDomino ∧
      (∃ x y, rDomino x y ≠ dead) ∧ (∃ x y, lDomino x y ≠ dead) ∧
      evolve rDomino = lDomino ∧ evolve lDomino = rDomino ∧ rDomino ≠ lDomino := by
  obtain ⟨hr,hl,_,hL,hne⟩ := nontrivial_two_cycle
  refine ⟨rDomino_finite,?_,rDomino_nonempty,?_,hr,hl,hne⟩
  · refine ⟨[(1,0),(1,1)],?_⟩
    intro x y
    simp [lDomino,dead,l]
    omega
  · exact ⟨1,0,by rw [hL]; decide +kernel⟩
end ResearchCommons.Claims.StatefulCertificates
