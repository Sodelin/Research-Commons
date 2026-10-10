import G7ActualCalendarGathering

/-! Finite exposure accounting for the complete gathering algorithm. This is
part of the actual calendar endpoint, not a physical independence assumption.
Uncompiled internal candidate, dot 2026-10-10. -/
namespace GProgram.G7.EdgeExposureAccounting
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw
open GProgram.G7.OriginalEdgeGathering GProgram.G7.ActualCalendarGathering
open scoped Classical NNReal
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

/-- Elapsed chronological duration until the first original entry/exit that
handles this population; unrelated event dates merely partition that sum. -/
noncomputable def untilTouch (N : RootedBinary V E X) (i : Option E) : List (Event V E) → ℝ
  | [] => 0
  | .interval t :: rest => (t:ℝ) + untilTouch N i rest
  | .exit e :: rest => if i = some e then 0 else untilTouch N i rest
  | .node v :: rest => if Opens N v i then 0 else untilTouch N i rest

/-- The algorithm's pending coordinate is an actual accumulated exposure,
with the one original population rate factored outside the complete sum. -/
theorem pending_eq_rate_mul_until (N : RootedBinary V E X) (r : PositivePairRates E)
    (ops : List (Event V E)) (i : Option E) :
    (gather N r ops).1 i = pairRate r i * untilTouch N i ops := by
  induction ops with
  | nil => simp [gather,untilTouch]
  | cons op ops ih =>
    cases op with
    | interval t => simp only [gather,Pi.add_apply,untilTouch,ih]; ring
    | exit e => by_cases h : i = some e <;> simp [gather,untilTouch,retain,h,ih]
    | node v => by_cases h : Opens N v i <;> simp [gather,untilTouch,retain,h,ih]

/-- A complete suffix with a supplied pending exposure bank. It is used only
for a finite append identity; all public source consumers start with zero. -/
noncomputable def gatherFrom (N : RootedBinary V E X) (r : PositivePairRates E)
    (pending : ExposureBank E) : List (Event V E) → ExposureBank E × List (Gathered V E)
  | [] => (pending,[])
  | .interval t :: rest =>
      let next := gatherFrom N r pending rest
      ((fun i => (t:ℝ)*pairRate r i) + next.1,next.2)
  | .exit e :: rest =>
      let next := gatherFrom N r pending rest
      (retain (fun i => i ≠ some e) next.1,.exit e :: next.2)
  | .node v :: rest =>
      let next := gatherFrom N r pending rest
      (retain (fun i => ¬ Opens N v i) next.1,.node v (retain (Opens N v) next.1) :: next.2)

lemma gatherFrom_zero (N : RootedBinary V E X) (r : PositivePairRates E) (ops : List (Event V E)) :
    gatherFrom N r 0 ops = gather N r ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih => cases op <;> simp only [gatherFrom,gather,ih]

lemma gather_append (N : RootedBinary V E X) (r : PositivePairRates E)
    (first last : List (Event V E)) :
    gather N r (first ++ last) =
      ((gatherFrom N r (gather N r last).1 first).1,
        (gatherFrom N r (gather N r last).1 first).2 ++ (gather N r last).2) := by
  induction first with
  | nil => simp [gatherFrom]
  | cons op ops ih =>
    cases op <;> simp only [List.cons_append,gather,gatherFrom,ih,List.cons_append]

lemma opens_disjoint (N : RootedBinary V E X) {v w : V} (h : v ≠ w) (i : Option E) :
    ¬ (Opens N v i ∧ Opens N w i) := by
  cases i <;> rintro ⟨hv,hw⟩ <;> exact h (hv.trans hw.symm)

lemma retain_idem (P : Option E → Prop) (w : ExposureBank E) : retain P (retain P w) = retain P w := by
  funext i
  by_cases h : P i <;> simp [retain,h]
lemma retain_commute (P Q : Option E → Prop) (w : ExposureBank E) :
    retain P (retain Q w) = retain Q (retain P w) := by
  funext i
  by_cases hp : P i <;> by_cases hq : Q i <;> simp [retain,hp,hq]

/-- Explicit scalar date recursion, without any source-kernel premise. -/
noncomputable def untilDate (mark : ℝ → Prop) : ℝ → List ℝ → ℝ
  | _,[] => 0
  | a,b::bs => b-a + if mark b then 0 else untilDate mark b bs

/-- Summing all intervening chronological fragments reaches the first marked
boundary exactly. This is the telescope used for the original edge exit. -/
theorem untilDate_first_mark (mark : ℝ → Prop) (a stop : ℝ) (dates : List ℝ)
    (ordered : (a::dates).Pairwise (· < ·)) (present : stop ∈ dates)
    (at_stop : mark stop) (no_earlier : ∀ d ∈ dates, d < stop → ¬ mark d) :
    untilDate mark a dates = stop-a := by
  induction dates generalizing a with
  | nil => simp at present
  | cons b bs ih =>
    rcases List.pairwise_cons.mp ordered with ⟨ha,hbs⟩
    rcases List.mem_cons.mp present with he | htail
    · subst b
      simp [untilDate,at_stop]
    · have hb : b < stop := (List.pairwise_cons.mp hbs).1 stop htail
      have hm : ¬ mark b := no_earlier b (by simp) hb
      rw [untilDate,if_neg hm,ih b hbs htail at_stop
        (fun d hd hlt => no_earlier d (List.mem_cons_of_mem b hd) hlt)]
      ring

/-- Original finite edge target/source dates are the only two relevant marks.
There is no metric-bin mark and no artificial frontier cut in this contract. -/
noncomputable def endpointDate (N : RootedBinary V E X) (C : Calendar N.graph) (i : Option E) (a : ℝ) : Prop :=
  match i with
  | none => a = C.age N.root
  | some e => a = C.age (N.graph.target e) ∨ a = C.age (N.graph.source e)

lemma whole_edge_date_telescope (N : RootedBinary V E X) (C : Calendar N.graph)
    (e : E) (dates : List ℝ)
    (ordered : (C.age (N.graph.target e)::dates).Pairwise (· < ·))
    (present : C.age (N.graph.source e) ∈ dates) :
    untilDate (endpointDate N C (some e)) (C.age (N.graph.target e)) dates =
      C.age (N.graph.source e) - C.age (N.graph.target e) := by
  apply untilDate_first_mark _ _ _ dates ordered present
  · exact Or.inr rfl
  · intro d hd hlt hm
    rcases hm with htarget | hsource
    · have h := (List.pairwise_cons.mp ordered).1 d hd
      rw [htarget] at h
      exact lt_irrefl _ h
    · rw [hsource] at hlt
      exact lt_irrefl _ hlt


def Touches (N : RootedBinary V E X) (i : Option E) : Event V E → Prop
  | .interval _ => False
  | .exit e => i = some e
  | .node v => Opens N v i

def Clockless : Event V E → Prop
  | .interval _ => False
  | _ => True

lemma untilTouch_clockless_append (N : RootedBinary V E X) (i : Option E)
    (front rest : List (Event V E)) (hc : ∀ op ∈ front, Clockless op) :
    untilTouch N i (front++rest) =
      if ∃ op ∈ front, Touches N i op then 0 else untilTouch N i rest := by
  induction front with
  | nil => simp
  | cons op front ih =>
    have hhead := hc op (by simp)
    have htail := fun q hq => hc q (List.mem_cons_of_mem op hq)
    cases op with
    | interval t => exact False.elim hhead
    | exit e =>
      by_cases hi : i = some e
      · simp [List.cons_append,untilTouch,hi,Touches]
      · simp [List.cons_append,untilTouch,hi,Touches,ih htail]
    | node v =>
      by_cases hi : Opens N v i
      · simp [List.cons_append,untilTouch,hi,Touches]
      · simp [List.cons_append,untilTouch,hi,Touches,ih htail]

lemma boundary_clockless (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ)
    (op : Event V E) (h : op ∈ boundaryEvents N C a) : Clockless op := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨e,_,rfl⟩ := List.mem_map.mp h
    trivial
  · obtain ⟨v,_,rfl⟩ := List.mem_map.mp h
    trivial

lemma boundary_has_touch_iff (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ) (i : Option E) :
    (∃ op ∈ boundaryEvents N C a, Touches N i op) ↔ endpointDate N C i a := by
  cases i <;>
    simp [boundaryEvents,Touches,Opens,endpointDate,List.mem_append,List.mem_map,
      Finset.mem_toList,Finset.mem_filter,eq_comm,or_comm]

lemma untilTouch_boundary_append (N : RootedBinary V E X) (C : Calendar N.graph)
    (a : ℝ) (i : Option E) (rest : List (Event V E)) :
    untilTouch N i (boundaryEvents N C a ++ rest) =
      if endpointDate N C i a then 0 else untilTouch N i rest := by
  rw [untilTouch_clockless_append N i _ rest (boundary_clockless N C a),boundary_has_touch_iff]

/-- Every intervening unrelated date is included, and its duration telescopes.
No independent interval-variable substitution is performed. -/
theorem generated_tail_until_date (N : RootedBinary V E X) (C : Calendar N.graph)
    (a : ℝ) (dates : List ℝ) (ordered : (a::dates).Pairwise (· < ·)) (i : Option E) :
    untilTouch N i (tailEvents N C a dates) = untilDate (endpointDate N C i) a dates := by
  induction dates generalizing a with
  | nil => rfl
  | cons b bs ih =>
    have ho := List.pairwise_cons.mp ordered
    have hab : a < b := ho.1 b (by simp)
    rw [tailEvents,untilTouch,untilTouch_boundary_append]
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hab.le),ih b ho.2]
    rfl

/-- The pending coordinate immediately after the original entry-date batch
is EXACTLY the whole original edge exposure, once its scheduled source date
is present. Calendar completeness supplies that final premise. -/
theorem actual_entry_tail_exposure (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (e : E) (dates : List ℝ)
    (ordered : (C.age (N.graph.target e)::dates).Pairwise (· < ·))
    (present : C.age (N.graph.source e) ∈ dates) :
    (gather N r (tailEvents N C (C.age (N.graph.target e)) dates)).1 (some e) =
      r.edge e * (C.age (N.graph.source e)-C.age (N.graph.target e)) := by
  rw [pending_eq_rate_mul_until,generated_tail_until_date N C _ dates ordered,
    whole_edge_date_telescope N C e dates ordered present]
  rfl

end GProgram.G7.EdgeExposureAccounting
