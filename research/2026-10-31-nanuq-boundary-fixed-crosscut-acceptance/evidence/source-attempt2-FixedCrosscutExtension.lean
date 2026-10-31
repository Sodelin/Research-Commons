import CrosscutClosedCells

set_option debug.skipKernelTC false
/-! UNCOMPILED prescribed crosscut extension. The cell topology is DERIVED
from original continuous crosscuts; no new order/collar certificate is input. -/
namespace Nanuq.RelativeCrosscut
open Set Schoenflies

 theorem inverse_agrees {S T B B' : Set Plane} {F G f g : Plane → Plane}
    (hFG : IsHomeoOn F G S T) (hfg : IsHomeoOn f g B B')
    (hBS : B ⊆ S) (hF : EqOn F f B) : EqOn G g B' := by
  intro y hy
  have hx := hfg.mapsTo_inv hy
  have he : F (g y) = y := (hF hx).trans (hfg.invOn.2 hy)
  calc G y = G (F (g y)) := congrArg G he.symm
       _ = g y := hFG.invOn.1 (hBS hx)

 theorem identity_homeo (S : Set Plane) : IsHomeoOn id id S S := by
  exact ⟨fun _ hx => hx,fun _ hx => hx,continuous_id.continuousOn,
    continuous_id.continuousOn,fun _ _ => rfl,fun _ _ => rfl⟩

/-- Construct the actual cell-boundary map by identity on A and m on P.
The fixed-endpoint premise belongs to the prescribed map, not to the source drawing. -/
theorem boundary_map {A P Q : Set Plane} {p q : Plane} {m n : Plane → Plane}
    (hA : IsArcBetween A p q) (hP : IsArcBetween P p q) (hQ : IsArcBetween Q p q)
    (hAP : A ∩ P = {p,q}) (hAQ : A ∩ Q = {p,q})
    (hmn : IsHomeoOn m n P Q) (hfix : EqOn m id {p,q}) :
    IsHomeoOn (paste A id m) (paste A id n) (A ∪ P) (A ∪ Q) ∧
    EqOn (paste A id m) id A ∧ EqOn (paste A id m) m P := by
  have hnfix : EqOn n id {p,q} := by
    intro z hz
    have hzP : z ∈ P := (hAP.symm ▸ hz : z ∈ A ∩ P).2
    have hmz : m z = z := hfix hz
    simpa only [hmz] using hmn.invOn.1 hzP
  have hf : EqOn id m (A ∩ P) := by
    intro z hz; exact (hfix (hAP ▸ hz)).symm
  have hg : EqOn id n (A ∩ Q) := by
    intro z hz; exact (hnfix (hAQ ▸ hz)).symm
  exact ⟨glue_two_closed hA.isArc.isClosed hP.isArc.isClosed
    hA.isArc.isClosed hQ.isArc.isClosed (identity_homeo A) hmn hf hg,
    fun _ hz => paste_of_mem hz,paste_eq_second hf⟩

 theorem bounded_crosscut_fixed_extension
    {C P Q A₁ A₂ : Set Plane} {p q : Plane} {m n : Plane → Plane}
    (hC : IsJordanCurve C) (hcut : IsCutPair C p q A₁ A₂)
    (hP : IsArcBetween P p q) (hQ : IsArcBetween Q p q)
    (hPC : P ∩ C = {p,q}) (hQC : Q ∩ C = {p,q})
    (hPI : P \ {p,q} ⊆ inside C) (hQI : Q \ {p,q} ⊆ inside C)
    (hmn : IsHomeoOn m n P Q) (hfix : EqOn m id {p,q}) :
    ∃ H : Plane ≃ₜ Plane, EqOn H id (C ∪ outside C) ∧ EqOn H m P := by
  have hAP (A : Set Plane) (hA : IsArcBetween A p q) (hAC : A ⊆ C) :
      A ∩ P = {p,q} := by
    apply Subset.antisymm
    · intro z hz; exact hPC ▸ ⟨hz.2,hAC hz.1⟩
    · rintro z (rfl | rfl)
      · exact ⟨hA.left_mem,hP.left_mem⟩
      · exact ⟨hA.right_mem,hP.right_mem⟩
  have hAQ (A : Set Plane) (hA : IsArcBetween A p q) (hAC : A ⊆ C) :
      A ∩ Q = {p,q} := by
    apply Subset.antisymm
    · intro z hz; exact hQC ▸ ⟨hz.2,hAC hz.1⟩
    · rintro z (rfl | rfl)
      · exact ⟨hA.left_mem,hQ.left_mem⟩
      · exact ⟨hA.right_mem,hQ.right_mem⟩
  obtain ⟨hc₁,hc₂,hcov,hint,hE₁,hE₂⟩ := closed_crosscut_cells hC hcut hP hPC hPI
  obtain ⟨hc₁',hc₂',hcov',hint',hE₁',hE₂'⟩ := closed_crosscut_cells hC hcut hQ hQC hQI
  obtain ⟨hb₁,hb₁A,hb₁P⟩ := boundary_map hcut.fst hP hQ
    (hAP A₁ hcut.fst hcut.fst_subset) (hAQ A₁ hcut.fst hcut.fst_subset) hmn hfix
  obtain ⟨hb₂,hb₂A,hb₂P⟩ := boundary_map hcut.snd hP hQ
    (hAP A₂ hcut.snd hcut.snd_subset) (hAQ A₂ hcut.snd hcut.snd_subset) hmn hfix
  obtain ⟨F₁,G₁,h₁,hF₁⟩ := closed_interior_extension squareExtension hc₁ hc₁' hb₁
  obtain ⟨F₂,G₂,h₂,hF₂⟩ := closed_interior_extension squareExtension hc₂ hc₂' hb₂
  let D₁ := (A₁ ∪ P) ∪ inside (A₁ ∪ P)
  let D₂ := (A₂ ∪ P) ∪ inside (A₂ ∪ P)
  let T₁ := (A₁ ∪ Q) ∪ inside (A₁ ∪ Q)
  let T₂ := (A₂ ∪ Q) ∪ inside (A₂ ∪ Q)
  let E := C ∪ outside C
  have hs₁ : IsClosed D₁ := isClosed_union_inside (jordan_curve_theorem hc₁)
  have hs₂ : IsClosed D₂ := isClosed_union_inside (jordan_curve_theorem hc₂)
  have ht₁ : IsClosed T₁ := isClosed_union_inside (jordan_curve_theorem hc₁')
  have ht₂ : IsClosed T₂ := isClosed_union_inside (jordan_curve_theorem hc₂')
  have he : IsClosed E := isClosed_union_outside (jordan_curve_theorem hC)
  have hFA₁ : EqOn F₁ id A₁ := fun z hz => (hF₁ (Or.inl hz)).trans (hb₁A hz)
  have hFA₂ : EqOn F₂ id A₂ := fun z hz => (hF₂ (Or.inl hz)).trans (hb₂A hz)
  have hFP₁ : EqOn F₁ m P := fun z hz => (hF₁ (Or.inr hz)).trans (hb₁P hz)
  have hFP₂ : EqOn F₂ m P := fun z hz => (hF₂ (Or.inr hz)).trans (hb₂P hz)
  have hGA₁ : EqOn G₁ id A₁ := inverse_agrees h₁ (identity_homeo A₁)
    (fun _ hz => Or.inl (Or.inl hz)) hFA₁
  have hGA₂ : EqOn G₂ id A₂ := inverse_agrees h₂ (identity_homeo A₂)
    (fun _ hz => Or.inl (Or.inl hz)) hFA₂
  have hGQ₁ : EqOn G₁ n Q := inverse_agrees h₁ hmn
    (fun _ hz => Or.inl (Or.inr hz)) hFP₁
  have hGQ₂ : EqOn G₂ n Q := inverse_agrees h₂ hmn
    (fun _ hz => Or.inl (Or.inr hz)) hFP₂
  have hFF : EqOn F₁ F₂ (D₁ ∩ D₂) := by
    intro z hz
    have hzP : z ∈ P := hint ▸ hz
    exact (hFP₁ hzP).trans (hFP₂ hzP).symm
  have hGG : EqOn G₁ G₂ (T₁ ∩ T₂) := by
    intro z hz
    have hzQ : z ∈ Q := hint' ▸ hz
    exact (hGQ₁ hzQ).trans (hGQ₂ hzQ).symm
  let F := paste D₁ F₁ F₂
  let G := paste T₁ G₁ G₂
  have hFG : IsHomeoOn F G (D₁ ∪ D₂) (T₁ ∪ T₂) :=
    glue_two_closed hs₁ hs₂ ht₁ ht₂ h₁ h₂ hFF hGG
  have hFD₁ : EqOn F F₁ D₁ := fun _ hz => paste_of_mem hz
  have hFD₂ : EqOn F F₂ D₂ := paste_eq_second hFF
  have hGT₁ : EqOn G G₁ T₁ := fun _ hz => paste_of_mem hz
  have hGT₂ : EqOn G G₂ T₂ := paste_eq_second hGG
  have hFEC : EqOn F id ((D₁ ∪ D₂) ∩ E) := by
    rintro z ⟨hz,hzE⟩
    rcases hz with hz | hz
    · exact (hFD₁ hz).trans (hFA₁ (hE₁ ▸ ⟨hz,hzE⟩))
    · exact (hFD₂ hz).trans (hFA₂ (hE₂ ▸ ⟨hz,hzE⟩))
  have hGEC : EqOn G id ((T₁ ∪ T₂) ∩ E) := by
    rintro z ⟨hz,hzE⟩
    rcases hz with hz | hz
    · exact (hGT₁ hz).trans (hGA₁ (hE₁' ▸ ⟨hz,hzE⟩))
    · exact (hGT₂ hz).trans (hGA₂ (hE₂' ▸ ⟨hz,hzE⟩))
  have htotal := glue_two_closed (hs₁.union hs₂) he (ht₁.union ht₂) he
    hFG (identity_homeo E) hFEC hGEC
  have hwhole : (D₁ ∪ D₂) ∪ E = univ := by
    change (((A₁ ∪ P) ∪ inside (A₁ ∪ P)) ∪ ((A₂ ∪ P) ∪ inside (A₂ ∪ P))) ∪ E = _
    rw [hcov]
    exact union_inside_union_outside C
  have hwhole' : (T₁ ∪ T₂) ∪ E = univ := by
    change (((A₁ ∪ Q) ∪ inside (A₁ ∪ Q)) ∪ ((A₂ ∪ Q) ∪ inside (A₂ ∪ Q))) ∪ E = _
    rw [hcov']
    exact union_inside_union_outside C
  rw [hwhole,hwhole'] at htotal
  refine ⟨htotal.homeomorphOfUniv, ?_, ?_⟩
  · exact paste_eq_second hFEC
  · intro z hz
    have hzD₁ : z ∈ D₁ := Or.inl (Or.inr hz)
    change paste (D₁ ∪ D₂) F id z = m z
    rw [paste_of_mem (Or.inl hzD₁),hFD₁ hzD₁,hFP₁ hz]

#print axioms bounded_crosscut_fixed_extension
end Nanuq.RelativeCrosscut
