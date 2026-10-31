import ResearchCommons.MSCI.JC69GuardedCalendarQuotient
import ResearchCommons.MSCI.JC69ActivatedPrefix

/-! WORKING UNCOMPILED source. Original contemporaneous sampling prefix.
Dot (OpenAI), 31 October 2026. No claim of completed prefix cancellation
until actual prefix support, calendar time and exposure joins are supplied. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69SamplingPrefix
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryLocations UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceCalendarTiming
open GProgram.SourceForestKingmanPopulationProjection
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Occupation
open ResearchCommons.MSCI.JC69CurrentPartition ResearchCommons.MSCI.JC69EndpointWeight
open ResearchCommons.MSCI.JC69FixedBankBoundary ResearchCommons.MSCI.JC69ActivatedPrefix
open ResearchCommons.MSCI.JC69CalendarOccupation ResearchCommons.MSCI.JC69WeightedCalendar
open ResearchCommons.MSCI.JC69GuardedCalendarQuotient
open GProgram.G2.FaithfulPairAgeDecoration GProgram.G2.ActualCalendarTrace
open GProgram.G2.CalendarDecoration
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

def SingletonBlocks (s : State V E Copy) : Prop :=
  ∀ B ∈ currentBlocks s, ∃ x : Copy, B = {x}

def Dormant (N : RootedBinary V E X) (sample : Copy → X) (s : Code N sample) : Prop :=
  ∀ x : Copy, copyLocation (state s) x = .node (N.leaf (sample x))

lemma dormant_choice_empty (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : Dormant N sample s) : IsEmpty (Choice N s) := by
  refine ⟨fun p => ?_⟩
  have hl := (Finset.mem_offDiag.mp p.2.property).1
  have hp := Finset.mem_filter.mp hl
  have h := hs p.2.val.1
  change (state s).location ((state s).ancestor p.2.val.1) = _ at h
  rw [s.property.forest.representative _ hp.1] at h
  exact originalPlace_not_node N p.1 _ (hp.2.symm.trans h)

lemma dormant_step_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : Dormant N sample s)
    {d : Code N sample} (hd : d ∈ (sourceStep N r s).support) : d = s := by
  letI := dormant_choice_empty N s hs
  obtain ⟨p,_,hp⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  cases p with
  | none => exact hp.symm
  | some p => exact isEmptyElim p

lemma dormant_iteration_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : ℕ) (s : Code N sample) (hs : Dormant N sample s)
    {d : Code N sample} (hd : d ∈ (sourceIteration N r k s).support) : d = s := by
  induction k with
  | zero => simpa only [sourceIteration,PMF.mem_support_pure_iff] using hd
  | succ k ih =>
      obtain ⟨m,hm,hmd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      have he := dormant_step_support N r s hs hm
      subst m
      exact ih hmd

lemma dormant_time_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (h : ℝ≥0) (s : Code N sample) (hs : Dormant N sample s)
    {d : Code N sample} (hd : d ∈ (sourceTimeKernel N r h s).support) : d = s := by
  obtain ⟨k,_,hk⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact dormant_iteration_support N r k s hs hk

/-- Original boundaries preserve descendant blocks, not literal Code identity. -/
lemma boundary_blocks_support (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N b s).support) : currentBlocks (state d) = currentBlocks (state s) := by
  have hp (H : GProgram.G2.OriginalHybridParents N) (coin : AtNode (state s) H.hybrid → Bool) :
      currentBlocks (state (pulseCode H s coin)) = currentBlocks (state s) := by
    have ho := admitted_observation N (pulse H (state s) coin)
      (pulse_source_valid H sample (state s) s.property coin)
    exact congrArg Prod.fst ho
  cases b with
  | exit e =>
      have he : d = exitCode N s e := by simpa only [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d; exact congrArg Prod.fst (exit_observation N s e)
  | ordinary e degree =>
      have he : d = ordinaryCode N s e := by simpa only [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d; exact congrArg Prod.fst (ordinary_observation N s e)
  | root =>
      have he : d = rootCode N s := by simpa only [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d; exact congrArg Prod.fst (root_observation N s)
  | common H =>
      have he : d = pulseCode H s (fun _ => (state s).register H.hybrid) := by
        simpa only [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d; exact hp H _
  | independent H gamma =>
      obtain ⟨coin,_,hc⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
      rw [← hc]; exact hp H coin

lemma singleton_boundary_support (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (s : Code N sample) (hs : SingletonBlocks (state s))
    {d : Code N sample} (hd : d ∈ (boundaryKernel N b s).support) : SingletonBlocks (state d) := by
  intro B hB
  rw [boundary_blocks_support N b s hd] at hB
  exact hs B hB

lemma dormant_exit_support (N : RootedBinary V E X) {sample : Copy → X}
    (e : E) (s : Code N sample) (hs : Dormant N sample s) : Dormant N sample (exitCode N s e) := by
  intro x
  rw [exitCode_copyLocation,hs x]
  rfl

lemma dormant_node_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (c : ℝ) (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c)
    (v : V) (hv : C.age v < c) (s : Code N sample) (hs : Dormant N sample s)
    {d : Code N sample}
    (hd : d ∈ (boundaryKernel N (originalNodeOperation N H gamma common v) s).support) :
    Dormant N sample d := by
  intro x
  have hm := actual_original_node_kernel_movement N H gamma common v s hd x
  have hn : copyLocation (state s) x ≠ .node v := by
    rw [hs x]
    intro he
    have hvx := congrArg C.age (Location.node.inj he)
    rw [hc x] at hvx
    exact (ne_of_lt hv) hvx.symm
  simpa only [NodeMovement,if_neg hn,hs x] using hm

lemma boundary_word_singleton (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bs : List (BoundaryOperation N)) (s : Code N sample)
    (hs : SingletonBlocks (state s)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (bs.map ProgramStep.boundary) s).support) :
    SingletonBlocks (state d) := by
  induction bs generalizing s with
  | nil =>
      have he : d = s := by simpa only [List.map_nil,sourceProgram,PMF.mem_support_pure_iff] using hd
      simpa only [he] using hs
  | cons b bs ih =>
      obtain ⟨m,hm,hmd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih m (singleton_boundary_support N b s hs hm) hmd

lemma exit_word_dormant (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (es : List E) (s : Code N sample) (hs : Dormant N sample s)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (es.map (fun e => .boundary (.exit e))) s).support) :
    Dormant N sample d := by
  induction es generalizing s with
  | nil =>
      have he : d = s := by simpa only [List.map_nil,sourceProgram,PMF.mem_support_pure_iff] using hd
      simpa only [he] using hs
  | cons e es ih =>
      obtain ⟨m,hm,hmd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      have he : m = exitCode N s e := by simpa only [boundaryKernel,PMF.mem_support_pure_iff] using hm
      subst m
      exact ih _ (dormant_exit_support N e s hs) hmd

lemma node_word_dormant (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (c : ℝ)
    (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) (vs : List V)
    (hv : ∀ v ∈ vs, C.age v < c) (s : Code N sample) (hs : Dormant N sample s)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r
      (vs.map (fun v => .boundary (originalNodeOperation N H gamma common v))) s).support) :
    Dormant N sample d := by
  induction vs generalizing s with
  | nil =>
      have he : d = s := by simpa only [List.map_nil,sourceProgram,PMF.mem_support_pure_iff] using hd
      simpa only [he] using hs
  | cons v vs ih =>
      obtain ⟨m,hm,hmd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih (fun w hw => hv w (by simp [hw])) m
        (dormant_node_support N C H gamma common c hc v (hv v (by simp)) s hs hm) hmd

lemma whole_boundary_singleton (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (a : ℝ) (s : Code N sample)
    (hs : SingletonBlocks (state s)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (boundaryOperations N C H gamma common a) s).support) :
    SingletonBlocks (state d) := by
  let es := (Finset.univ.filter (fun e : E => C.age (N.graph.source e) = a)).toList
  let vs := (Finset.univ.filter (fun v : V => C.age v = a)).toList
  have heq : boundaryOperations N C H gamma common a =
      (es.map BoundaryOperation.exit ++ vs.map (originalNodeOperation N H gamma common)).map ProgramStep.boundary := by
    simp [boundaryOperations,es,vs,List.map_append,List.map_map,Function.comp_def]
  rw [heq] at hd
  exact boundary_word_singleton N r _ s hs hd

lemma whole_boundary_dormant (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (c : ℝ)
    (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) (a : ℝ) (ha : a < c)
    (s : Code N sample) (hs : Dormant N sample s) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (boundaryOperations N C H gamma common a) s).support) :
    Dormant N sample d := by
  rw [boundaryOperations,sourceProgram_append] at hd
  obtain ⟨m,hm,hmd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have he := exit_word_dormant N r _ s hs hm
  exact node_word_dormant N C H gamma common r c hc _
    (fun v hv => ((Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2).trans_lt ha) m he hmd

/-- Strong sampling invariant: singleton blocks through c, dormant locations
strictly before c. At c actual routing is allowed, with no instantaneous merger. -/
def SamplingInvariant (N : RootedBinary V E X) (sample : Copy → X) (c a : ℝ)
    (s : Code N sample) : Prop := SingletonBlocks (state s) ∧ (a < c → Dormant N sample s)

lemma tail_sampling_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (c : ℝ)
    (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) (dates : List ℝ) (a : ℝ)
    (hordered : dates.Pairwise (· < ·)) (hafter : ∀ b ∈ dates, a < b)
    (hcut : ∀ b ∈ dates, b ≤ c) (s : Code N sample)
    (hs : SamplingInvariant N sample c a s) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (calendarTail N C H gamma common a dates) s).support) :
    SamplingInvariant N sample c (finalDate a dates) d := by
  induction dates generalizing a s with
  | nil =>
      have he : d = s := by simpa only [calendarTail,sourceProgram,PMF.mem_support_pure_iff] using hd
      simpa only [finalDate,he] using hs
  | cons b bs ih =>
      have hab := hafter b (by simp)
      have hbc := hcut b (by simp)
      have hdorm := hs.2 (hab.trans_le hbc)
      change d ∈ ((sourceTimeKernel N r (Real.toNNReal (b-a)) s).bind
        (sourceProgram N r (boundaryOperations N C H gamma common b ++ calendarTail N C H gamma common b bs))).support at hd
      obtain ⟨m,hm,hmd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      have he := dormant_time_support N r _ s hdorm hm
      subst m
      rw [sourceProgram_append] at hmd
      obtain ⟨z,hz,hzd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hmd
      have hzInv : SamplingInvariant N sample c b z :=
        ⟨whole_boundary_singleton N C H gamma common r b s hs.1 hz,
          fun hb => whole_boundary_dormant N C H gamma common r c hc b hb s hdorm hz⟩
      have ho := List.pairwise_cons.mp hordered
      exact ih b ho.2 ho.1 (fun u hu => hcut u (by simp [hu])) z hzInv hzd

lemma dates_le_final (a : ℝ) (dates : List ℝ) (ho : dates.Pairwise (· < ·))
    (ha : ∀ b ∈ dates, a < b) : a ≤ finalDate a dates ∧ ∀ b ∈ dates, b ≤ finalDate a dates := by
  induction dates generalizing a with
  | nil => exact ⟨le_rfl,by simp⟩
  | cons b bs ih =>
      have hh := List.pairwise_cons.mp ho
      have ht := ih b hh.2 hh.1
      refine ⟨(ha b (by simp)).le.trans ht.1,?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with he | he
      · simpa only [he,finalDate] using ht.1
      · exact ht.2 u he

lemma initial_singleton_dormant (N : RootedBinary V E X) (sample : Copy → X) (register : V → Bool) :
    SingletonBlocks (state (initialCode N sample register)) ∧ Dormant N sample (initialCode N sample register) := by
  have ho := admitted_observation N (initial N sample register) (initial_source_valid N sample register)
  constructor
  · intro B hB
    have hb := congrArg Prod.fst ho
    change currentBlocks (state (initialCode N sample register)) = currentBlocks (initial N sample register) at hb
    rw [hb] at hB
    obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hB
    exact ⟨l,hl.symm⟩
  · intro x
    exact congrFun (congrArg Prod.snd ho) x

/-- Actual initialized whole-date prefix remains singleton through sampling.
Dormant locations are asserted only STRICTLY before sampling. -/
theorem actual_sampling_prefix_support (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (c : ℝ) (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) (k : ℕ)
    (hcut : prefixDate N C k ≤ c) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (initializedPrefix N C H gamma common k)
      (initialCode N sample register)).support) :
    SamplingInvariant N sample c (prefixDate N C k) d := by
  have hne : sortedOriginalDates N C ≠ [] := by
    intro he
    have hm := original_date_scheduled N C N.root
    rw [he] at hm
    exact List.not_mem_nil hm
  obtain ⟨a,dates,heq⟩ := List.exists_cons_of_ne_nil hne
  have ho := original_dates_strict N C
  rw [heq] at ho
  have hp := List.pairwise_cons.mp ho
  have ht : (dates.take k).Pairwise (· < ·) := hp.2.take
  have ha : ∀ b ∈ dates.take k, a < b := fun b hb => hp.1 b (List.mem_of_mem_take hb)
  have hfinal : finalDate a (dates.take k) ≤ c := by simpa only [prefixDate,heq] using hcut
  have hbnd := dates_le_final a (dates.take k) ht ha
  have hi := initial_singleton_dormant N sample register
  rw [initializedPrefix,heq,sourceProgram_append] at hd
  obtain ⟨s,hs,hsd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hstart : SamplingInvariant N sample c a s :=
    ⟨whole_boundary_singleton N C H gamma common r a _ hi.1 hs,
      fun hac => whole_boundary_dormant N C H gamma common r c hc a hac _ hi.2 hs⟩
  simpa only [prefixDate,heq] using tail_sampling_support N C H gamma common r c hc
    (dates.take k) a ht ha (fun b hb => (hbnd.2 b hb).trans hfinal) s hstart hsd

lemma wellLabelled_singleton_leaf (t : Genealogy Copy) (ht : t.WellLabelled)
    {x : Copy} (hx : t.leaves = {x}) : ∃ y : Copy, t = .leaf y := by
  cases t with
  | leaf y => exact ⟨y,rfl⟩
  | graft a b =>
      have ha : witness a = x := Finset.mem_singleton.mp (by
        rw [← hx]; exact Finset.mem_union_left _ (witness_mem a))
      have hb : witness b = x := Finset.mem_singleton.mp (by
        rw [← hx]; exact Finset.mem_union_right _ (witness_mem b))
      have hab : witness a ∈ b.leaves := by rw [ha,← hb]; exact witness_mem b
      exact False.elim (Finset.disjoint_left.mp ht.2.2 (witness_mem a) hab)

lemma singleton_potential_zero (s : State V E Copy) (hs : Valid s) (hB : SingletonBlocks s)
    (q : Copy → Base) (leafAge : Copy → ℝ) (c : ℝ) (hc : ∀ x, leafAge x = c)
    (M : Copy → Copy → ℝ) : forestPotential q leafAge s M c = 0 := by
  apply Finset.sum_eq_zero
  intro l hl
  obtain ⟨x,hx⟩ := hB (s.genealogy l).leaves (Finset.mem_image.mpr ⟨l,hl,rfl⟩)
  obtain ⟨y,hy⟩ := wellLabelled_singleton_leaf (s.genealogy l) (hs.wellLabelled l hl) hx
  simp only [hy,potential,hc y,sub_self,mul_zero]

lemma calendar_time_append (N : RootedBinary V E X) (xs ys : List (ProgramStep N)) (a : ℝ) :
    calendarTime N (xs ++ ys) a = calendarTime N ys (calendarTime N xs a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => exact ih (segmentOffset N x a)

lemma boundary_word_time (N : RootedBinary V E X) (bs : List (BoundaryOperation N)) (a : ℝ) :
    calendarTime N (bs.map ProgramStep.boundary) a = a := by
  induction bs with
  | nil => rfl
  | cons b bs ih => exact ih

lemma whole_boundary_time (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (b a : ℝ) :
    calendarTime N (boundaryOperations N C H gamma common b) a = a := by
  let es := (Finset.univ.filter (fun e : E => C.age (N.graph.source e) = b)).toList
  let vs := (Finset.univ.filter (fun v : V => C.age v = b)).toList
  have heq : boundaryOperations N C H gamma common b =
      (es.map BoundaryOperation.exit ++ vs.map (originalNodeOperation N H gamma common)).map ProgramStep.boundary := by
    simp [boundaryOperations,es,vs,List.map_append,List.map_map,Function.comp_def]
  rw [heq,boundary_word_time]

lemma tail_calendar_time (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (dates : List ℝ) (a : ℝ)
    (ho : dates.Pairwise (· < ·)) (ha : ∀ b ∈ dates, a < b) :
    calendarTime N (calendarTail N C H gamma common a dates) a = finalDate a dates := by
  induction dates generalizing a with
  | nil => rfl
  | cons b bs ih =>
      have hab := ha b (by simp)
      have hp := List.pairwise_cons.mp ho
      have he : a+(Real.toNNReal (b-a) : ℝ) = b := by
        rw [Real.coe_toNNReal _ (sub_nonneg.mpr hab.le)]; ring
      change calendarTime N (boundaryOperations N C H gamma common b ++ calendarTail N C H gamma common b bs)
        (a+(Real.toNNReal (b-a) : ℝ)) = finalDate b bs
      rw [he,calendar_time_append,whole_boundary_time]
      exact ih b hp.2 hp.1

theorem actual_prefix_calendar_time (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (k : ℕ) :
    calendarTime N (initializedPrefix N C H gamma common k) (firstOriginalDate N C) = prefixDate N C k := by
  have hne : sortedOriginalDates N C ≠ [] := by
    intro he
    have hm := original_date_scheduled N C N.root
    rw [he] at hm
    exact List.not_mem_nil hm
  obtain ⟨a,dates,heq⟩ := List.exists_cons_of_ne_nil hne
  have hf : a = firstOriginalDate N C := by
    have h := first_compiled_date_is_initial_boundary N C
    simpa only [heq,List.getElem_cons_zero] using h
  have ho := original_dates_strict N C
  rw [heq] at ho
  have hp := List.pairwise_cons.mp ho
  rw [initializedPrefix,prefixDate,heq,← hf,calendar_time_append,whole_boundary_time]
  exact tail_calendar_time N C H gamma common (dates.take k) a hp.2.take
    (fun b hb => hp.1 b (List.mem_of_mem_take hb))

lemma exists_prefix_finalDate (a : ℝ) (dates : List ℝ) (c : ℝ) (hc : c ∈ a::dates) :
    ∃ k : ℕ, finalDate a (dates.take k) = c := by
  induction dates generalizing a with
  | nil =>
      have he : c = a := by simpa only [List.mem_singleton] using hc
      exact ⟨0,he.symm⟩
  | cons b bs ih =>
      rcases List.mem_cons.mp hc with he | he
      · exact ⟨0,he.symm⟩
      · obtain ⟨k,hk⟩ := ih b he
        exact ⟨k+1,by simpa only [List.take_succ_cons,finalDate] using hk⟩

/-- The required cut is present in the original vertex agenda, not added as
an arbitrary external time. The scientific panel is nonempty. -/
theorem actual_sampling_cut_exists [Nonempty Copy] (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (c : ℝ) (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) :
    ∃ k : ℕ, prefixDate N C k = c := by
  let x : Copy := Classical.choice inferInstance
  have hm := original_date_scheduled N C (N.leaf (sample x))
  rw [hc x] at hm
  cases heq : sortedOriginalDates N C with
  | nil => rw [heq] at hm; exact False.elim (List.not_mem_nil hm)
  | cons a dates =>
      rw [heq] at hm
      obtain ⟨k,hk⟩ := exists_prefix_finalDate a dates c hm
      exact ⟨k,by simpa only [prefixDate,heq] using hk⟩

lemma actual_sampling_singleton_ae (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (c : ℝ) (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) (k : ℕ)
    (hcut : prefixDate N C k = c) :
    let ops := initializedPrefix N C H gamma common k
    let s := initialCode N sample register
    ∀ᵐ past ∂actualCalendarTraceLaw N r ops s, SingletonBlocks (state (calendarEnd N ops s past)) := by
  let ops := initializedPrefix N C H gamma common k
  let s := initialCode N sample register
  let p := sourceProgram N r ops s
  have hs : ∀ᵐ d ∂p.toMeasure, d ∈ p.support := by
    rw [← p.restrict_toMeasure_support]
    exact ae_restrict_mem p.support_countable.measurableSet
  have ha : ∀ᵐ d ∂p.toMeasure, SingletonBlocks (state d) := by
    filter_upwards [hs] with d hd
    exact (actual_sampling_prefix_support N C sample register H gamma common r c hc k hcut.le hd).1
  change ∀ᵐ d ∂(sourceProgram N r ops s).toMeasure, SingletonBlocks (state d) at ha
  rw [← actual_calendar_endpoint_law N r ops s] at ha
  exact ae_of_ae_map (calendar_end_measurable N ops s).aemeasurable ha

/-- The original initialization factor cancels its actual pre-sampling
occupation on the SAME record law. It is not assumed <=1 or discarded.
Original success/normalization and exposure suppliers are reused unchanged. -/
theorem actual_initial_factor_cancellation (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (L : ℕ) (q : Fin L → Copy → Base) (c : ℝ)
    (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) (k : ℕ)
    (hcut : prefixDate N C k = c) :
    let ops := initializedPrefix N C H gamma common k
    let s := initialCode N sample register
    ∀ᵐ past ∂actualCalendarTraceLaw N r ops s,
      initialPotentialWeight N C sample register L q * calendarWeight N L q ops s past = 1 := by
  let ops := initializedPrefix N C H gamma common k
  let s := initialCode N sample register
  let leafAge := fun x : Copy => C.age (N.leaf (sample x))
  let M := fun x (_ : Copy) => leafAge x
  have ht : calendarTime N ops (firstOriginalDate N C) = c :=
    (actual_prefix_calendar_time N C H gamma common k).trans hcut
  have hE := ae_all_iff.mpr (fun j : Fin L =>
    actual_calendar_exposure N r (q j) leafAge ops s (firstOriginalDate N C) M)
  filter_upwards [hE,actual_sampling_singleton_ae N C sample register H gamma common r c hc k hcut,
    actual_calendar_weight_exponential N r L q ops s] with past he hs hw
  have hz (j : Fin L) : forestPotential (q j) leafAge (state s) M (firstOriginalDate N C) +
      calendarOccupation N (q j) ops s past = 0 := by
    have h := he j
    rw [ht,singleton_potential_zero _ (calendarEnd N ops s past).property.forest hs (q j) leafAge c hc] at h
    exact h.symm
  have hsum : (∑ j, forestPotential (q j) leafAge (state s) M (firstOriginalDate N C)) +
      (∑ j, calendarOccupation N (q j) ops s past) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun j _ => hz j)
  rw [hw]
  change ENNReal.ofReal (Real.exp (-((4/3:ℝ) * ∑ j,
      forestPotential (q j) leafAge (state s) M (firstOriginalDate N C)))) *
    ENNReal.ofReal (Real.exp (-((4/3:ℝ) * ∑ j, calendarOccupation N (q j) ops s past))) = 1
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),← Real.exp_add]
  have hexp : -((4/3:ℝ) * ∑ j, forestPotential (q j) leafAge (state s) M (firstOriginalDate N C)) +
      -((4/3:ℝ) * ∑ j, calendarOccupation N (q j) ops s past) = 0 := by
    linarith [hsum]
  rw [hexp]
  simp

#print axioms actual_sampling_prefix_support
#print axioms actual_prefix_calendar_time
#print axioms actual_sampling_cut_exists
#print axioms actual_initial_factor_cancellation
end ResearchCommons.MSCI.JC69SamplingPrefix
