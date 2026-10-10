import UnifiedLean.Source.SourceBoundaryLocations
import UnifiedLean.Source.SourceCalendarTiming

/-!
# Physical calendar support of actual original boundary batches

Contributor: dot, 2026-10-02. Reuses actual source exits/current-node kernels
and derives source temporal support instead of treating SourceValid as calendar
admission. Every original edge/node ID at a date is processed by the compiled
batch, with original parent edges and retained registers. Full sorted-agenda
induction and exponential-clock path/readout binding follow this boundary gate.
-/
namespace UnifiedLean.Source.SourceCalendarPhysicalSupport
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

def BoundaryReady (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ)
    (s : State V E Copy) : Prop := EpochCompatible N C a a s

def AfterExits (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ)
    (s : State V E Copy) : Prop :=
  BoundaryReady N C a s ∧ ∀ x : Copy, ∀ e : E, copyLocation s x = .edge e → a < C.age (N.graph.source e)

def AfterNodes (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ)
    (s : State V E Copy) : Prop :=
  AfterExits N C a s ∧ ∀ x : Copy, ∀ v : V, copyLocation s x = .node v → a < C.age v

lemma exit_preserves_ready (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} {a : ℝ} (s : Code N sample) (e : E)
    (he : C.age (N.graph.source e) = a) (hs : BoundaryReady N C a (state s)) :
    BoundaryReady N C a (state (exitCode N s e)) := by
  intro x
  rw [exitCode_copyLocation]
  unfold exitLocation
  by_cases hp : copyLocation (state s) x = .edge e
  · rw [if_pos hp]
    change a ≤ C.age (N.graph.source e)
    rw [he]
  · rw [if_neg hp]
    exact hs x

lemma exit_removes_edge (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) (x : Copy) :
    copyLocation (state (exitCode N s e)) x ≠ .edge e := by
  rw [exitCode_copyLocation]
  unfold exitLocation
  split_ifs with h
  · intro hh
    cases hh
  · exact h

lemma exit_never_creates_edge (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e f : E) (x : Copy)
    (h : copyLocation (state s) x ≠ .edge f) :
    copyLocation (state (exitCode N s e)) x ≠ .edge f := by
  rw [exitCode_copyLocation]
  unfold exitLocation
  split_ifs
  · intro hh
    cases hh
  · exact h

/-- All actual compiled exit operations are performed, with no original edge
reintroduced by a later exit. No source state is spatially refitted. -/
theorem exit_list_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (r : PositivePairRates E) {a : ℝ} (es done : List E)
    (he : ∀ e ∈ es, C.age (N.graph.source e) = a) (s : Code N sample)
    (hs : BoundaryReady N C a (state s))
    (hno : ∀ x : Copy, ∀ e ∈ done, copyLocation (state s) x ≠ .edge e)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (es.map (fun e => .boundary (.exit e))) s).support) :
    BoundaryReady N C a (state d) ∧
      ∀ x : Copy, ∀ e ∈ done ++ es, copyLocation (state d) x ≠ .edge e := by
  induction es generalizing done s with
  | nil =>
      have hds : d = s := by simpa only [List.map_nil,sourceProgram,PMF.mem_support_pure_iff] using hd
      subst d
      exact ⟨hs,by simpa using hno⟩
  | cons e es ih =>
      have hdest : d ∈ (sourceProgram N r (es.map (fun e => .boundary (.exit e))) (exitCode N s e)).support := by
        simpa only [List.map_cons,sourceProgram,sourceProgramStep,boundaryKernel,PMF.pure_bind] using hd
      have hready := exit_preserves_ready N C s e (he e (by simp)) hs
      have hdone : ∀ x : Copy, ∀ f ∈ done ++ [e], copyLocation (state (exitCode N s e)) x ≠ .edge f := by
        intro x f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact exit_never_creates_edge N s e f x (hno x f hf)
        · have hfe : f = e := by simpa using hf
          subst f
          exact exit_removes_edge N s e x
      have h := ih (done ++ [e]) (fun f hf => he f (List.mem_cons_of_mem e hf))
        (exitCode N s e) hready hdone hdest
      refine ⟨h.1,?_⟩
      intro x f hf
      apply h.2 x f
      simpa only [List.append_assoc,List.singleton_append] using hf

/-- Processing precisely all ORIGINAL edges that end at a makes every
remaining edge population strictly active above a. -/
theorem actual_exit_batch_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (r : PositivePairRates E) (a : ℝ) (s : Code N sample)
    (hs : BoundaryReady N C a (state s)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r
      ((Finset.univ.filter (fun e : E => C.age (N.graph.source e) = a)).toList.map
        (fun e => .boundary (.exit e))) s).support) : AfterExits N C a (state d) := by
  let es := (Finset.univ.filter (fun e : E => C.age (N.graph.source e) = a)).toList
  have hh := exit_list_support N C r es [] (by
    intro e he
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2) s hs (by simp) hd
  refine ⟨hh.1,?_⟩
  intro x e hp
  have hbound := hh.1 x
  rw [hp] at hbound
  have hne : C.age (N.graph.source e) ≠ a := by
    intro he
    have hm : e ∈ es := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
    exact hh.2 x e (by simpa using hm) hp
  exact (lt_or_eq_of_le hbound.2).resolve_right hne.symm

lemma node_move_preserves_after_exits (N : RootedBinary V E X) (C : Calendar N.graph)
    {a : ℝ} {v : V} (hv : C.age v = a) {old new : Location V E}
    (hready : LocationInEpoch N C a a old)
    (hstrict : ∀ e : E, old = .edge e → a < C.age (N.graph.source e))
    (hm : NodeMovement N v old new) :
    LocationInEpoch N C a a new ∧
      (∀ e : E, new = .edge e → a < C.age (N.graph.source e)) := by
  unfold NodeMovement at hm
  by_cases hn : old = .node v
  · rw [if_pos hn] at hm
    by_cases hr : v = N.root
    · rw [if_pos hr] at hm
      subst new
      refine ⟨⟨rfl,?_⟩,?_⟩
      · rw [← hr,hv]
      · intro e he
        cases he
    · rw [if_neg hr] at hm
      obtain ⟨e,he,hnew⟩ := hm
      subst new
      have ht : C.age (N.graph.target e) = a := by rw [he,hv]
      have ho : a < C.age (N.graph.source e) := by simpa only [ht] using C.edge_older e
      refine ⟨⟨ht.le,ho.le⟩,?_⟩
      intro f hf
      have heq : e = f := Location.edge.inj hf
      simpa only [← heq] using ho
  · rw [if_neg hn] at hm
    subst new
    exact ⟨hready,hstrict⟩

lemma node_move_never_creates_node (N : RootedBinary V E X) {v u : V} {old new : Location V E}
    (hm : NodeMovement N v old new) (hu : old ≠ .node u) : new ≠ .node u := by
  unfold NodeMovement at hm
  by_cases hn : old = .node v
  · rw [if_pos hn] at hm
    split_ifs at hm
    · rw [hm]
      intro h
      cases h
    · obtain ⟨e,_,he⟩ := hm
      rw [he]
      intro h
      cases h
  · rw [if_neg hn] at hm
    simpa only [hm] using hu

lemma node_move_removes_node (N : RootedBinary V E X) {v : V} {old new : Location V E}
    (hm : NodeMovement N v old new) : new ≠ .node v := by
  by_cases hn : old = .node v
  · unfold NodeMovement at hm
    rw [if_pos hn] at hm
    split_ifs at hm
    · rw [hm]
      intro h
      cases h
    · obtain ⟨e,_,he⟩ := hm
      rw [he]
      intro h
      cases h
  · exact node_move_never_creates_node N hm hn

/-- The actual node PMF retains physical active locations and eliminates its
own pending original node, for all current-root Bernoulli/Common outcomes. -/
theorem actual_node_after_exits (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} {a : ℝ} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (hv : C.age v = a) (s : Code N sample)
    (hs : AfterExits N C a (state s)) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N (originalNodeOperation N H gamma common v) s).support) :
    AfterExits N C a (state d) ∧ ∀ x : Copy, copyLocation (state d) x ≠ .node v := by
  have hm := fun x => actual_original_node_kernel_movement N H gamma common v s hd x
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro x
    exact (node_move_preserves_after_exits N C hv (hs.1 x) (hs.2 x) (hm x)).1
  · intro x
    exact (node_move_preserves_after_exits N C hv (hs.1 x) (hs.2 x) (hm x)).2
  · intro x
    exact node_move_removes_node N (hm x)

lemma sourceProgram_append (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (xs ys : List (ProgramStep N)) (s : Code N sample) :
    sourceProgram N r (xs ++ ys) s = (sourceProgram N r xs s).bind (sourceProgram N r ys) := by
  induction xs generalizing s with
  | nil => simp only [List.nil_append,sourceProgram,PMF.pure_bind]
  | cons op xs ih =>
      change ((sourceProgramStep N r op s).bind (sourceProgram N r (xs ++ ys))) =
        ((sourceProgramStep N r op s).bind (sourceProgram N r xs)).bind (sourceProgram N r ys)
      rw [PMF.bind_bind]
      congr 1
      funext d
      exact ih d

/-- All original node operations at a boundary are processed; a later node
entry/pulse cannot reintroduce an already processed pending node. -/
theorem node_list_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) {a : ℝ} (vs done : List V)
    (hv : ∀ v ∈ vs, C.age v = a) (s : Code N sample)
    (hs : AfterExits N C a (state s))
    (hno : ∀ x : Copy, ∀ v ∈ done, copyLocation (state s) x ≠ .node v)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (vs.map (fun v =>
      .boundary (originalNodeOperation N H gamma common v))) s).support) :
    AfterExits N C a (state d) ∧
      ∀ x : Copy, ∀ v ∈ done ++ vs, copyLocation (state d) x ≠ .node v := by
  induction vs generalizing done s with
  | nil =>
      have hds : d = s := by simpa only [List.map_nil,sourceProgram,PMF.mem_support_pure_iff] using hd
      subst d
      exact ⟨hs,by simpa using hno⟩
  | cons v vs ih =>
      change d ∈ ((boundaryKernel N (originalNodeOperation N H gamma common v) s).bind
        (sourceProgram N r (vs.map (fun v => .boundary (originalNodeOperation N H gamma common v))))).support at hd
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      have hh := actual_node_after_exits N C H gamma common v (hv v (by simp)) s hs hm
      have hdone : ∀ x : Copy, ∀ u ∈ done ++ [v], copyLocation (state m) x ≠ .node u := by
        intro x u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact node_move_never_creates_node N
            (actual_original_node_kernel_movement N H gamma common v s hm x) (hno x u hu)
        · have huv : u = v := by simpa using hu
          subst u
          exact hh.2 x
      have h := ih (done ++ [v]) (fun u hu => hv u (List.mem_cons_of_mem v hu)) m hh.1 hdone hdm
      refine ⟨h.1,?_⟩
      intro x u hu
      apply h.2 x u
      simpa only [List.append_assoc,List.singleton_append] using hu

/-- After all ORIGINAL current-date nodes, remaining pending nodes are
strictly in the future. All independent/Common outcomes are included. -/
theorem actual_node_batch_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (a : ℝ) (s : Code N sample)
    (hs : AfterExits N C a (state s)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r
      ((Finset.univ.filter (fun v : V => C.age v = a)).toList.map
        (fun v => .boundary (originalNodeOperation N H gamma common v))) s).support) :
    AfterNodes N C a (state d) := by
  let vs := (Finset.univ.filter (fun v : V => C.age v = a)).toList
  have hh := node_list_support N C H gamma common r vs [] (by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2) s hs (by simp) hd
  refine ⟨hh.1,?_⟩
  intro x v hp
  have hbound := hh.1.1 x
  rw [hp] at hbound
  have hne : C.age v ≠ a := by
    intro hv
    have hm : v ∈ vs := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩)
    exact hh.2 x v (by simpa using hm) hp
  exact (lt_or_eq_of_le hbound).resolve_right hne.symm

/-- Physical source support of the COMPLETE constructed original date batch:
all actual edge exits first, then all actual node entries/pulses. -/
theorem actual_original_boundary_batch_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (a : ℝ) (s : Code N sample)
    (hs : BoundaryReady N C a (state s)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (boundaryOperations N C H gamma common a) s).support) :
    AfterNodes N C a (state d) := by
  rw [boundaryOperations,sourceProgram_append] at hd
  obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact actual_node_batch_support N C H gamma common r a m
    (actual_exit_batch_support N C r a s hs hm) hdm

#print axioms actual_exit_batch_support
#print axioms node_move_preserves_after_exits
#print axioms actual_node_after_exits
#print axioms actual_original_boundary_batch_support
end UnifiedLean.Source.SourceCalendarPhysicalSupport
