import G7ExactLawResourceGame

/-!
Conditional semantic transfer for the EXISTING exact-law game. Every field is
a proof obligation for the actual source/provider join, not an admission flag
or a construction of physical sources, native polynomials or a QE selector.
Representatives need not be unique. Targets must be preserved individually.
-/
namespace Astra.G7ExactLawSourceTransfer

open GProgram.G7.ExactLawResourceGame

variable {S M A Y T R : Type*}

/-- A relation on admitted points with BOTH coverage directions. The same
related pair supplies every response in an entire history and every action.
Original action/resource semantics are retained, including exact updates. -/
structure Representation (physical : Experiment S A Y T R)
    (symbolic : Experiment M A Y T R) where
  related : S → M → Prop
  physical_admitted : ∀ s m, related s m → physical.admitted s
  symbolic_admitted : ∀ s m, related s m → symbolic.admitted m
  to_model : ∀ s, physical.admitted s → ∃ m, related s m
  to_source : ∀ m, symbolic.admitted m → ∃ s, related s m
  target_eq : ∀ s m, related s m → physical.target s = symbolic.target m
  response_eq : ∀ s m, related s m → ∀ a, physical.response s a = symbolic.response m a
  legal_iff : ∀ u a, physical.legal u a ↔ symbolic.legal u a
  update_eq : ∀ u a, physical.update u a = symbolic.update u a

variable {physical : Experiment S A Y T R} {symbolic : Experiment M A Y T R}
variable (rep : Representation physical symbolic)

theorem related_consistent_iff (s : S) (m : M) (hr : rep.related s m)
    (h : History A Y) : Consistent physical h s ↔ Consistent symbolic h m := by
  constructor
  · rintro ⟨_,hh⟩
    exact ⟨rep.symbolic_admitted s m hr,fun ay hay =>
      (rep.response_eq s m hr ay.1).symm.trans (hh ay hay)⟩
  · rintro ⟨_,hh⟩
    exact ⟨rep.physical_admitted s m hr,fun ay hay =>
      (rep.response_eq s m hr ay.1).trans (hh ay hay)⟩

theorem consistent_has_model (h : History A Y) (s : S)
    (hs : Consistent physical h s) :
    ∃ m, rep.related s m ∧ Consistent symbolic h m := by
  obtain ⟨m,hr⟩ := rep.to_model s hs.1
  exact ⟨m,hr,(related_consistent_iff rep s m hr h).mp hs⟩

theorem consistent_has_source (h : History A Y) (m : M)
    (hm : Consistent symbolic h m) :
    ∃ s, rep.related s m ∧ Consistent physical h s := by
  obtain ⟨s,hr⟩ := rep.to_source m hm.1
  exact ⟨s,hr,(related_consistent_iff rep s m hr h).mpr hm⟩

theorem homogeneous_iff (h : History A Y) :
    Homogeneous physical h ↔ Homogeneous symbolic h := by
  constructor
  · intro hh m n hm hn
    obtain ⟨s,hs,hs'⟩ := consistent_has_source rep h m hm
    obtain ⟨t,ht,ht'⟩ := consistent_has_source rep h n hn
    exact (rep.target_eq s m hs).symm.trans ((hh s t hs' ht').trans (rep.target_eq t n ht))
  · intro hh s t hs ht
    obtain ⟨m,hm,hm'⟩ := consistent_has_model rep h s hs
    obtain ⟨n,hn,hn'⟩ := consistent_has_model rep h t ht
    exact (rep.target_eq s m hm).trans ((hh m n hm' hn').trans (rep.target_eq t n hn).symm)

theorem winning_iff (n : Nat) (h : History A Y) (u : R) :
    Winning physical n h u ↔ Winning symbolic n h u := by
  induction n generalizing h u with
  | zero => exact homogeneous_iff rep h
  | succ n ih =>
    constructor
    · rintro (hh | ⟨a,ha,hy⟩)
      · exact Or.inl ((homogeneous_iff rep h).mp hh)
      · refine Or.inr ⟨a,(rep.legal_iff u a).mp ha,fun y => ?_⟩
        simpa only [rep.update_eq u a] using (ih ((a,y)::h) (physical.update u a)).mp (hy y)
    · rintro (hh | ⟨a,ha,hy⟩)
      · exact Or.inl ((homogeneous_iff rep h).mpr hh)
      · refine Or.inr ⟨a,(rep.legal_iff u a).mpr ha,fun y => ?_⟩
        apply (ih ((a,y)::h) (physical.update u a)).mpr
        simpa only [rep.update_eq u a] using hy y

/-- The very same plan is valid after transfer. This is stronger than merely
asserting some identifying plan exists; no effective plan is extracted here. -/
theorem valid_plan_iff {n : Nat} (plan : Plan A Y T n)
    (h : History A Y) (u : R) :
    Valid physical plan h u ↔ Valid symbolic plan h u := by
  induction plan generalizing h u with
  | stop q =>
    constructor
    · intro hp m hm
      obtain ⟨s,hr,hs⟩ := consistent_has_source rep h m hm
      exact (rep.target_eq s m hr).symm.trans (hp s hs)
    · intro hp s hs
      obtain ⟨m,hr,hm⟩ := consistent_has_model rep h s hs
      exact (rep.target_eq s m hr).trans (hp m hm)
  | ask a next ih =>
    constructor
    · rintro ⟨ha,hy⟩
      refine ⟨(rep.legal_iff u a).mp ha,fun y => ?_⟩
      simpa only [rep.update_eq u a] using (ih y ((a,y)::h) (physical.update u a)).mp (hy y)
    · rintro ⟨ha,hy⟩
      refine ⟨(rep.legal_iff u a).mpr ha,fun y => ?_⟩
      apply (ih y ((a,y)::h) (physical.update u a)).mpr
      simpa only [rep.update_eq u a] using hy y

theorem physical_run_of_symbolic_valid {n : Nat} (plan : Plan A Y T n)
    (h : History A Y) (u : R) (hp : Valid symbolic plan h u)
    (s : S) (hs : Consistent physical h s) :
    run physical plan s = physical.target s :=
  valid_run_identifies physical plan h u ((valid_plan_iff rep plan h u).mpr hp) s hs

/-- A symbolic ambiguity lifts to TWO admitted original points fitting the
same ENTIRE history. No single pair defeating every policy is asserted. -/
theorem physical_pair_of_symbolic_pair (h : History A Y) (m n : M)
    (hm : Consistent symbolic h m) (hn : Consistent symbolic h n)
    (different : symbolic.target m ≠ symbolic.target n) :
    ∃ s t, Consistent physical h s ∧ Consistent physical h t ∧
      physical.target s ≠ physical.target t := by
  obtain ⟨s,hs,hs'⟩ := consistent_has_source rep h m hm
  obtain ⟨t,ht,ht'⟩ := consistent_has_source rep h n hn
  refine ⟨s,t,hs',ht',?_⟩
  intro he
  exact different ((rep.target_eq s m hs).symm.trans (he.trans (rep.target_eq t n ht)))

theorem physical_pair_of_symbolic_loss (n : Nat) (h : History A Y) (u : R)
    (loss : ¬ Winning symbolic n h u) :
    ∃ s t, Consistent physical h s ∧ Consistent physical h t ∧
      physical.target s ≠ physical.target t := by
  obtain ⟨m,k,hm,hk,hd⟩ := losing_has_full_history_pair symbolic n h u loss
  exact physical_pair_of_symbolic_pair rep h m k hm hk hd

end Astra.G7ExactLawSourceTransfer
