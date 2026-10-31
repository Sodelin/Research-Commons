import ResearchCommons.MSCI.JC69CommonCountIndex
import UnifiedLean.Source.SourceBoundaryKernels

/-! Actual fixed-original-register boundary observation quotient.
UNCOMPILED candidate, dot (OpenAI), 31 October 2026. Current block coins are
reindexed, not independently assigned per original copy. Re-banking is admission,
not a claim of reachability. No supported S bound or calendar product assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69FixedBankBoundary
open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceForestPulseMeasure
open ResearchCommons.MSCI.JC69CurrentPartition ResearchCommons.MSCI.JC69SourceRootQuotient
open ResearchCommons.MSCI.JC69EndpointWeight
open scoped Classical BigOperators ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- SourceValid does not restrict the register. This changes no forest,
original-copy population, or descendant-admission data. -/
def reBank (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (sigma : V → Bool) : Code N sample :=
  ⟨{s.val with register := sigma},
    ⟨⟨s.property.forest.ancestor_live,s.property.forest.representative,
      s.property.forest.leaf_fiber,s.property.forest.wellLabelled⟩,
      s.property.original_descendant⟩⟩

theorem actual_reBank_observation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (sigma : V → Bool) :
    observeCode N (reBank N s sigma) = observeCode N s ∧
      (state (reBank N s sigma)).register = sigma := ⟨rfl,rfl⟩

lemma admitted_observation (N : RootedBinary V E X) {sample : Copy → X}
    (s : State V E Copy) (hs : SourceValid N sample s) :
    observeCode N (admittedCode N sample s hs) = observeState s := by
  apply Prod.ext
  · exact decode_encode_blocks N.root s hs.forest
  · funext x
    exact decode_encode_copyLocation N.root s hs.forest x

lemma observe_transport (s : State V E Copy) (f : Location V E → Location V E)
    (event : SourceEvent V E Copy) :
    observeState (transport s (f ∘ s.location) event) =
      (currentBlocks s,fun x => f (copyLocation s x)) := rfl

lemma exit_observation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (edge : E) :
    observeCode N (exitCode N s edge) =
      ((observeCode N s).1,fun x => exitLocation N edge ((observeCode N s).2 x)) := by
  rw [exitCode,admitted_observation]
  rfl

lemma ordinary_observation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (edge : E) :
    observeCode N (ordinaryCode N s edge) =
      ((observeCode N s).1,fun x => ordinaryLocation N edge ((observeCode N s).2 x)) := by
  rw [ordinaryCode,admitted_observation]
  rfl

lemma root_observation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) :
    observeCode N (rootCode N s) =
      ((observeCode N s).1,fun x => rootLocation N ((observeCode N s).2 x)) := by
  rw [rootCode,admitted_observation]
  rfl

/-- Repackage the ACTUAL AtNode subtype, without changing its current owners. -/
def atNodeLiveEquiv (s : State V E Copy) (v : V) :
    AtNode s v ≃ {a : LiveRoot s // s.location a.val = .node v} where
  toFun a := ⟨⟨a.val,a.property.1⟩,a.property.2⟩
  invFun a := ⟨a.val.val,a.val.property,a.property⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨⟨a,ha⟩,hp⟩; rfl

def matchingAtNodeEquiv (s t : State V E Copy) (hs : Valid s) (ht : Valid t)
    (hB : currentBlocks s = currentBlocks t)
    (hLoc : ∀ x, copyLocation s x = copyLocation t x) (v : V) : AtNode s v ≃ AtNode t v :=
  (atNodeLiveEquiv s v).trans
    (((liveRootEquiv s t hs ht hB).subtypeEquiv (fun a => by
      change s.location a.val = .node v ↔
        t.location (matchingRoot s t hB a).val = .node v
      rw [matchingRoot_location s t hs ht hB hLoc a])).trans (atNodeLiveEquiv t v).symm)

lemma matchingRoot_ancestor (s t : State V E Copy) (hs : Valid s) (ht : Valid t)
    (hB : currentBlocks s = currentBlocks t) (x : Copy) :
    (matchingRoot s t hB ⟨s.ancestor x,hs.ancestor_live x⟩).val = t.ancestor x := by
  have hx : x ∈ (s.genealogy (s.ancestor x)).leaves :=
    (hs.leaf_fiber _ (hs.ancestor_live x) x).mpr rfl
  have hy : x ∈ (t.genealogy (matchingRoot s t hB ⟨s.ancestor x,hs.ancestor_live x⟩).val).leaves := by
    rw [matchingRoot_block]
    exact hx
  exact ((ht.leaf_fiber _ (matchingRoot s t hB ⟨s.ancestor x,hs.ancestor_live x⟩).property x).mp hy).symm

/-- Pull back CURRENT-owner coin assignments along the actual matching blocks. -/
def transportCoin {A B : Type*} (e : A ≃ B) (coin : A → Bool) : B → Bool :=
  fun b => coin (e.symm b)

lemma actual_pulse_observation {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (s t : State V E Copy)
    (hs : Valid s) (ht : Valid t) (hB : currentBlocks s = currentBlocks t)
    (hLoc : ∀ x, copyLocation s x = copyLocation t x)
    (coin : AtNode s H.hybrid → Bool) :
    observeState (pulse H s coin) =
      observeState (pulse H t (transportCoin (matchingAtNodeEquiv s t hs ht hB hLoc H.hybrid) coin)) := by
  apply Prod.ext
  · exact hB
  · funext x
    let e := matchingAtNodeEquiv s t hs ht hB hLoc H.hybrid
    have hx := hLoc x
    change s.location (s.ancestor x) = t.location (t.ancestor x) at hx
    by_cases hp : s.location (s.ancestor x) = .node H.hybrid
    · have hq : t.location (t.ancestor x) = .node H.hybrid := hx.symm.trans hp
      let a : AtNode s H.hybrid := ⟨s.ancestor x,hs.ancestor_live x,hp⟩
      let b : AtNode t H.hybrid := ⟨t.ancestor x,ht.ancestor_live x,hq⟩
      have hab : e a = b := by
        apply Subtype.ext
        exact matchingRoot_ancestor s t hs ht hB x
      have hc : transportCoin e coin b = coin a := by
        rw [← hab]
        exact congrArg coin (e.symm_apply_apply a)
      change (pulse H s coin).location (s.ancestor x) =
        (pulse H t (transportCoin e coin)).location (t.ancestor x)
      change (pulse H s coin).location a.val = (pulse H t (transportCoin e coin)).location b.val
      rw [pulse_routes_current_ancestor H s coin a,pulse_routes_current_ancestor H t (transportCoin e coin) b,hc]
    · have hq : t.location (t.ancestor x) ≠ .node H.hybrid := fun h => hp (hx.trans h)
      simp [observeState,copyLocation,pulse,transport,hp,hq,hx]

lemma coded_pulse_observation {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s t : Code N sample)
    (hobs : observeCode N s = observeCode N t)
    (coin : AtNode (state s) H.hybrid → Bool) :
    observeCode N (pulseCode H s coin) =
      observeCode N (pulseCode H t
        (transportCoin (matchingAtNodeEquiv (state s) (state t) s.property.forest t.property.forest
          (congrArg Prod.fst hobs) (fun x => congrFun (congrArg Prod.snd hobs) x) H.hybrid) coin)) := by
  rw [pulseCode,pulseCode,admitted_observation,admitted_observation]
  exact actual_pulse_observation H (state s) (state t) s.property.forest t.property.forest _ _ coin

/-- The product law is invariant under the actual CURRENT-owner bijection,
including Bernoulli parameters zero and one. No per-copy redraw is introduced. -/
lemma transportCoin_measurePreserving {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (gamma : unitInterval) :
    MeasurePreserving (transportCoin e) (independentCoinMeasure A gamma)
      (independentCoinMeasure B gamma) := by
  have hm := measurePreserving_piCongrLeft (fun _ : B => bitMeasure gamma) e
  have he : (⇑(MeasurableEquiv.piCongrLeft (fun _ : B => Bool) e)) = transportCoin e := by
    funext coin b
    simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply,transportCoin]
  rw [he] at hm
  exact hm

lemma transportCoin_pmf {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (gamma : unitInterval) :
    (currentCoinPMF A gamma).map (transportCoin e) = currentCoinPMF B gamma := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  unfold currentCoinPMF
  rw [Measure.toPMF_toMeasure,Measure.toPMF_toMeasure]
  exact (transportCoin_measurePreserving e gamma).map_eq

/-- Actual independent original pulse descends to current blocks/populations. -/
theorem actual_independent_boundary_quotient {N : RootedBinary V E X}
    {sample : Copy → X} (H : GProgram.G2.OriginalHybridParents N) (gamma : unitInterval)
    (s t : Code N sample) (hobs : observeCode N s = observeCode N t) :
    (independentPulseKernel H gamma s).map (observeCode N) =
      (independentPulseKernel H gamma t).map (observeCode N) := by
  let e := matchingAtNodeEquiv (state s) (state t) s.property.forest t.property.forest
    (congrArg Prod.fst hobs) (fun x => congrFun (congrArg Prod.snd hobs) x) H.hybrid
  have hcoin := transportCoin_pmf e gamma
  rw [independentPulseKernel,independentPulseKernel,PMF.map_comp,PMF.map_comp,← hcoin,PMF.map_comp]
  congr 1
  funext coin
  exact coded_pulse_observation H s t hobs coin

/-- Exact original boundary law on a fixed once-drawn register fibre. -/
theorem actual_fixed_bank_boundary_quotient (N : RootedBinary V E X)
    {sample : Copy → X} (op : BoundaryOperation N) (s t : Code N sample)
    (hobs : observeCode N s = observeCode N t)
    (hreg : (state s).register = (state t).register) :
    (boundaryKernel N op s).map (observeCode N) =
      (boundaryKernel N op t).map (observeCode N) := by
  cases op with
  | exit edge => simp only [boundaryKernel,PMF.pure_map]; congr 1; rw [exit_observation,exit_observation,hobs]
  | ordinary edge degree => simp only [boundaryKernel,PMF.pure_map]; congr 1; rw [ordinary_observation,ordinary_observation,hobs]
  | root => simp only [boundaryKernel,PMF.pure_map]; congr 1; rw [root_observation,root_observation,hobs]
  | independent H gamma => exact actual_independent_boundary_quotient H gamma s t hobs
  | common H =>
    simp only [boundaryKernel,PMF.pure_map]
    congr 1
    have hp := coded_pulse_observation H s t hobs (fun _ => (state s).register H.hybrid)
    simpa [transportCoin,hreg] using hp

/-- Actual coded PMF operations preserve the original register exactly. -/
theorem actual_boundary_register_law (N : RootedBinary V E X)
    {sample : Copy → X} (op : BoundaryOperation N) (s : Code N sample) :
    (boundaryKernel N op s).map (fun d => (state d).register) = PMF.pure ((state s).register) := by
  cases op with
  | exit edge => simp [boundaryKernel,PMF.pure_map,exitCode,admittedCode,state,decodeSnapshot,encodeSnapshot,exitEdge,transport]
  | ordinary edge degree => simp [boundaryKernel,PMF.pure_map,ordinaryCode,admittedCode,state,decodeSnapshot,encodeSnapshot,enterEdge,transport]
  | root => simp [boundaryKernel,PMF.pure_map,rootCode,admittedCode,state,decodeSnapshot,encodeSnapshot,enterRoot,transport]
  | common H => simp [boundaryKernel,PMF.pure_map,pulseCode,admittedCode,state,decodeSnapshot,encodeSnapshot,pulse,transport]
  | independent H gamma =>
    rw [boundaryKernel,independentPulseKernel,PMF.map_comp]
    have hf : (fun d : Code N sample => (state d).register) ∘ pulseCode H s =
        Function.const (AtNode (state s) H.hybrid → Bool) ((state s).register) := by
      funext coin
      rfl
    rw [hf,PMF.map_const]

/-- A single count/bank-independent admitted representative can be re-banked
ONLY for boundary coefficients. No added representative existence premise. -/
theorem actual_boundary_representative (N : RootedBinary V E X)
    {sample : Copy → X} (op : BoundaryOperation N) (s representative : Code N sample)
    (hobs : observeCode N s = observeCode N representative) :
    (boundaryKernel N op s).map (observeCode N) =
      (boundaryKernel N op (reBank N representative (state s).register)).map (observeCode N) := by
  apply actual_fixed_bank_boundary_quotient N op
  · exact hobs.trans (actual_reBank_observation N representative (state s).register).1.symm
  · exact (actual_reBank_observation N representative (state s).register).2.symm

#print axioms actual_reBank_observation
#print axioms actual_independent_boundary_quotient
#print axioms actual_fixed_bank_boundary_quotient
#print axioms actual_boundary_register_law
#print axioms actual_boundary_representative
end ResearchCommons.MSCI.JC69FixedBankBoundary
