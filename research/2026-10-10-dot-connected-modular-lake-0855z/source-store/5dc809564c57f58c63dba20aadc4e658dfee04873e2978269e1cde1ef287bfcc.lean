import ActualObservationCutRefinement

/-! Finite analytical cut insertion on actual original source words.
Draft continuation: no new biological boundary or register operation. -/
namespace UnifiedLean.G6.FiniteCutSourceWord
open MeasureTheory Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open GProgram.G2.CalendarDecoration GProgram.G2.ChronologicalPathReadout
open CloudG3.ActualCalendarEndpointHistory CloudG3.ActualObservationCutRefinement
open CloudG3.ActualCalendarCutContext
open scoped Classical NNReal
variable {V E X Tag : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma refines_cons (N : RootedBinary V E X) (op : ProgramStep N)
    {a b : List (ProgramStep N)} (h : CutRefines N a b) :
    CutRefines N (op::a) (op::b) := by
  induction h with
  | refl a => exact .refl _
  | split pre post t u =>
      simpa using (CutRefines.split (op::pre) post t u)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

noncomputable def oneCutBin (bin : ℝ → Tag) (q : ℝ) (x : ℝ) : Tag × Bool :=
  (bin x, decide (q < x))

noncomputable def oneCutWord (N : RootedBinary V E X) (q : ℝ) :
    List (ProgramStep N × Tag) → ℝ → List (ProgramStep N × (Tag × Bool))
  | [],_ => []
  | (.boundary b,tag)::ws,offset =>
      (.boundary b,(tag,false)) :: oneCutWord N q ws offset
  | (.interval h,tag)::ws,offset =>
      if offset < q ∧ q < offset + (h:ℝ) then
        (.interval (Real.toNNReal (q-offset)),(tag,false)) ::
        (.interval (Real.toNNReal (offset+(h:ℝ)-q)),(tag,true)) ::
        oneCutWord N q ws (offset+(h:ℝ))
      else (.interval h,(tag,decide (q ≤ offset))) :: oneCutWord N q ws (offset+(h:ℝ))

lemma split_duration (offset q : ℝ) (h : ℝ≥0)
    (hcut : offset < q ∧ q < offset + (h:ℝ)) :
    Real.toNNReal (q-offset) + Real.toNNReal (offset+(h:ℝ)-q) = h := by
  apply NNReal.coe_injective
  simp only [NNReal.coe_add, Real.coe_toNNReal _ (by linarith : 0 ≤ q-offset),
    Real.coe_toNNReal _ (by linarith : 0 ≤ offset+(h:ℝ)-q)]
  ring

theorem one_cut_refines (N : RootedBinary V E X) (q : ℝ)
    (word : List (ProgramStep N × Tag)) (offset : ℝ) :
    CutRefines N (physicalOps N word) (physicalOps N (oneCutWord N q word offset)) := by
  induction word generalizing offset with
  | nil => exact .refl _
  | cons item ws ih =>
      rcases item with ⟨op,tag⟩
      cases op with
      | boundary b =>
          exact refines_cons N (.boundary b) (ih offset)
      | interval h =>
          by_cases hc : offset < q ∧ q < offset + (h:ℝ)
          · have hs := CutRefines.split ([] : List (ProgramStep N))
              (physicalOps N (oneCutWord N q ws (offset+(h:ℝ))))
              (Real.toNNReal (q-offset)) (Real.toNNReal (offset+(h:ℝ)-q))
            rw [split_duration offset q h hc] at hs
            exact (refines_cons N (.interval h) (ih (offset+(h:ℝ)))).trans
              (by simpa [oneCutWord,hc,physicalOps] using hs)
          · simpa [oneCutWord,hc,physicalOps] using
              refines_cons N (.interval h) (ih (offset+(h:ℝ)))

theorem one_cut_contract (N : RootedBinary V E X) (q : ℝ) (bin : ℝ → Tag)
    (word : List (ProgramStep N × Tag)) (offset : ℝ)
    (hw : wordBinContract N bin word offset) :
    wordBinContract N (oneCutBin bin q) (oneCutWord N q word offset) offset := by
  induction word generalizing offset with
  | nil => trivial
  | cons item ws ih =>
      rcases item with ⟨op,tag⟩
      cases op with
      | boundary b =>
          exact ⟨trivial,ih offset hw.2⟩
      | interval h =>
          change (∀ a : ℝ, offset < a → a < offset+(h:ℝ) → bin a = tag) ∧
            wordBinContract N bin ws (offset+(h:ℝ)) at hw
          by_cases hc : offset < q ∧ q < offset+(h:ℝ)
          · have ha : (Real.toNNReal (q-offset) : ℝ) = q-offset :=
              Real.coe_toNNReal _ (by linarith)
            have hb : (Real.toNNReal (offset+(h:ℝ)-q) : ℝ) = offset+(h:ℝ)-q :=
              Real.coe_toNNReal _ (by linarith)
            rw [oneCutWord,if_pos hc]
            change (∀ x : ℝ, offset < x → x < offset + (Real.toNNReal (q-offset) : ℝ) →
                oneCutBin bin q x = (tag,false)) ∧
              (∀ x : ℝ, offset + (Real.toNNReal (q-offset) : ℝ) < x →
                x < offset + (Real.toNNReal (q-offset) : ℝ) +
                  (Real.toNNReal (offset+(h:ℝ)-q) : ℝ) →
                oneCutBin bin q x = (tag,true)) ∧
              wordBinContract N (oneCutBin bin q) (oneCutWord N q ws (offset+(h:ℝ)))
                (offset + (Real.toNNReal (q-offset) : ℝ) +
                  (Real.toNNReal (offset+(h:ℝ)-q) : ℝ))
            rw [ha,hb]
            constructor
            · intro x hx hy
              apply Prod.ext
              · exact hw.1 x hx (by linarith)
              · simp [oneCutBin,show ¬q<x by linarith]
            · constructor
              · intro x hx hy
                apply Prod.ext
                · exact hw.1 x (by linarith) (by linarith)
                · simp [oneCutBin,show q<x by linarith]
              · have he : offset+(q-offset)+(offset+(h:ℝ)-q) = offset+(h:ℝ) := by ring
                rw [he]
                exact ih _ hw.2
          · rw [oneCutWord,if_neg hc]
            change (∀ x : ℝ, offset < x → x < offset+(h:ℝ) →
                oneCutBin bin q x = (tag,decide (q≤offset))) ∧
              wordBinContract N (oneCutBin bin q) (oneCutWord N q ws (offset+(h:ℝ)))
                (offset+(h:ℝ))
            refine ⟨?_,ih (offset+(h:ℝ)) hw.2⟩
            intro x hx hy
            apply Prod.ext
            · exact hw.1 x hx hy
            · by_cases hq : q ≤ offset
              · simp [oneCutBin,hq,show q<x by linarith]
              · have hn : ¬ q<x := by
                  intro hqx
                  exact hc ⟨lt_of_not_ge hq,by linarith⟩
                simp [oneCutBin,hq,hn]

/-- A finite tuple of threshold comparisons. Its rank gives the ordinary
finite-bin index, so no extra stochastic observation is introduced. -/
def CutTags : List ℝ → Type
  | [] => Unit
  | _::qs => CutTags qs × Bool

noncomputable def cutsBin : (qs : List ℝ) → ℝ → CutTags qs
  | [],_ => ()
  | q::qs,x => oneCutBin (cutsBin qs) q x

noncomputable def cutsWord (N : RootedBinary V E X) :
    (qs : List ℝ) → List (ProgramStep N) → ℝ → List (ProgramStep N × CutTags qs)
  | [],ops,_ => ops.map fun op => (op,())
  | q::qs,ops,offset => oneCutWord N q (cutsWord N qs ops offset) offset

theorem cuts_word_refines (N : RootedBinary V E X) (qs : List ℝ)
    (ops : List (ProgramStep N)) (offset : ℝ) :
    CutRefines N ops (physicalOps N (cutsWord N qs ops offset)) := by
  induction qs with
  | nil => simpa [cutsWord,physicalOps,List.map_map,Function.comp_def] using CutRefines.refl ops
  | cons q qs ih => exact ih.trans (one_cut_refines N q _ offset)

theorem cuts_word_contract (N : RootedBinary V E X) (qs : List ℝ)
    (ops : List (ProgramStep N)) (offset : ℝ) :
    wordBinContract N (cutsBin qs) (cutsWord N qs ops offset) offset := by
  induction qs with
  | nil =>
      induction ops generalizing offset with
      | nil => trivial
      | cons op ops ih =>
          cases op with
          | boundary b => exact ⟨trivial,ih offset⟩
          | interval h => exact ⟨by intro x hx hy; rfl, ih (offset+(h:ℝ))⟩
  | cons q qs ih => exact one_cut_contract N q _ _ offset ih

def bumpRank {n : ℕ} (p : Fin (n+1) × Bool) : Fin (n+2) :=
  ⟨p.1.val + if p.2 then 1 else 0, by
    have h := p.1.isLt
    cases p.2 <;> simp_all <;> omega⟩

def rankTag : (qs : List ℝ) → CutTags qs → Fin (qs.length+1)
  | [],_ => 0
  | _::qs,(tag,b) => bumpRank (rankTag qs tag,b)

noncomputable def rankBin (qs : List ℝ) (x : ℝ) : Fin (qs.length+1) :=
  rankTag qs (cutsBin qs x)

noncomputable def rankedWord (N : RootedBinary V E X) (qs : List ℝ)
    (ops : List (ProgramStep N)) (offset : ℝ) :
    List (ProgramStep N × Fin (qs.length+1)) :=
  (cutsWord N qs ops offset).map fun p => (p.1, rankTag qs p.2)

lemma physical_map_tag {Tag' : Type*} (N : RootedBinary V E X)
    (f : Tag → Tag') (word : List (ProgramStep N × Tag)) :
    physicalOps N (word.map fun p => (p.1,f p.2)) = physicalOps N word := by
  simp [physicalOps,List.map_map,Function.comp_def]

lemma contract_map_tag {Tag' : Type*} (N : RootedBinary V E X)
    (f : Tag → Tag') (bin : ℝ → Tag) (word : List (ProgramStep N × Tag))
    (offset : ℝ) (h : wordBinContract N bin word offset) :
    wordBinContract N (f ∘ bin) (word.map fun p => (p.1,f p.2)) offset := by
  induction word generalizing offset with
  | nil => trivial
  | cons p ws ih =>
      rcases p with ⟨op,tag⟩
      cases op with
      | boundary b => exact ⟨trivial,ih _ h.2⟩
      | interval t =>
          refine ⟨?_,ih _ h.2⟩
          intro x hx hy
          exact congrArg f (h.1 x hx hy)

theorem ranked_word_refines (N : RootedBinary V E X) (qs : List ℝ)
    (ops : List (ProgramStep N)) (offset : ℝ) :
    CutRefines N ops (physicalOps N (rankedWord N qs ops offset)) := by
  rw [rankedWord,physical_map_tag]
  exact cuts_word_refines N qs ops offset

theorem ranked_word_contract (N : RootedBinary V E X) (qs : List ℝ)
    (ops : List (ProgramStep N)) (offset : ℝ) :
    wordBinContract N (rankBin qs) (rankedWord N qs ops offset) offset :=
  contract_map_tag N (rankTag qs) (cutsBin qs) _ offset (cuts_word_contract N qs ops offset)

theorem rank_bin_measurable (qs : List ℝ) : Measurable (rankBin qs) := by
  induction qs with
  | nil => exact measurable_const
  | cons q qs ih =>
      have hb : Measurable (fun x : ℝ => decide (q<x)) := by
        have he : (fun x : ℝ => decide (q<x)) =
            (fun x : ℝ => if q<x then true else false) := by
          funext x
          split_ifs <;> simp_all
        rw [he]
        exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
          measurable_const measurable_const
      exact (measurable_of_countable (bumpRank (n := qs.length))).comp (ih.prodMk hb)

theorem rank_bin_val (qs : List ℝ) (x : ℝ) :
    (rankBin qs x).val = (qs.filter fun q => decide (q<x)).length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      change (rankBin qs x).val + (if decide (q<x) then 1 else 0) = _
      rw [ih]
      by_cases h : q<x <;> simp [h,List.filter,Nat.add_comm]

theorem rank_bin_zero (qs : List ℝ) (hq : ∀ q ∈ qs, 0 ≤ q) :
    rankBin qs 0 = 0 := by
  apply Fin.ext
  rw [rank_bin_val]
  have he : (qs.filter fun q => decide (q<0)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro q hm
    simpa using not_lt_of_ge (hq q hm)
  rw [he]
  rfl

theorem rank_bin_tail (qs : List ℝ) (cut x : ℝ)
    (hq : ∀ q ∈ qs, q ≤ cut) (hx : cut<x) :
    rankBin qs x = Fin.last qs.length := by
  apply Fin.ext
  rw [rank_bin_val]
  have he : (qs.filter fun q => decide (q<x)) = qs := by
    apply List.filter_eq_self.mpr
    intro q hm
    simpa using lt_of_le_of_lt (hq q hm) hx
  rw [he]
  rfl

/-- Literal actual source law at all finite cuts. Both subdivision and the
interval-bin contract are constructed, not supplied premises. -/
theorem actual_ranked_endpoint_history {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : UnifiedLean.Source.NativePairClockLaw.PositivePairRates E)
    (qs : List ℝ) (ops : List (ProgramStep N))
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ) :
    CloudG3.CompleteCalendarJointLaw.calendarJointPMF N r (rankBin qs)
      (rank_bin_measurable qs) ops s offset M =
      (GProgram.G2.SourceFiniteHistory.sourceHistoryLaw N r
        (physicalOps N (rankedWord N qs ops offset)) s).map
        (endpointHistoryReadout N (rankedWord N qs ops offset) s
          (fun a b => rankBin qs (M a b))) :=
  original_gamma_refined_endpoint_history N r (rankBin qs) (rank_bin_measurable qs)
    ops (rankedWord N qs ops offset) (ranked_word_refines N qs ops offset)
    s offset M (ranked_word_contract N qs ops offset)

end UnifiedLean.G6.FiniteCutSourceWord
