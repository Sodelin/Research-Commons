import G1ActualKInputFirstRecord

/-! The retained final own signature derives a literal actual K-input cut.
The opening-to-K gap contains only other-actor/base work; optional outside
identities do not create or move an own interface. -/
namespace G1OwnOpeningKInputCut
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1OwnProtocolSignatureTransport
open G1OwnProtocolBlockExtraction G1CanonicalInteriorInterfaceAdmission
open scoped Classical
variable {I S Base : Type*} [DecidableEq I]

lemma signature_nil_is_safe_for (owner : I) (ops : List (AsyncOperation I S Base))
    (hn : ownProtocolSignature owner ops = []) : ∀ op ∈ ops, SafeFor owner op := by
  intro op hm
  have hnot (h : ownedProtocolOp owner op = true) : False := by
    have hp : op ∈ ownProtocolSignature owner ops := List.mem_filter.mpr ⟨hm,h⟩
    rw [hn] at hp
    exact List.not_mem_nil hp
  cases op with
  | localStep other kernel =>
    change owner ≠ other
    intro he; exact hnot (by simp [ownedProtocolOp,he])
  | interface other kernel =>
    change owner ≠ other
    intro he; exact hnot (by simp [ownedProtocolOp,he])
  | exterior kernel => trivial

lemma actual_open_kernel_signature_cut (owner : I) (ops : List (AsyncOperation I S Base))
    (opening : Base × S → PMF (Base × S)) (kernel : S → PMF S)
    (tail : List (AsyncOperation I S Base))
    (hs : ownProtocolSignature owner ops = .interface owner opening :: .localStep owner kernel :: tail) :
    ∃ before gap later,
      ops = before ++ .interface owner opening :: (gap ++ .localStep owner kernel :: later) ∧
      (∀ op ∈ before, InteriorSafe owner op) ∧ (∀ op ∈ gap, SafeFor owner op) := by
  obtain ⟨before,rest,hb,hbefore,hrest⟩ := signature_cons_extract owner ops _ _ hs
  obtain ⟨gap,later,hg,hgap,_⟩ := signature_cons_extract owner rest _ _ hrest
  exact ⟨before,gap,later,by rw [hb,hg],signature_nil_is_interior_safe owner before hbefore,
    signature_nil_is_safe_for owner gap hgap⟩

/-- Literal K-input cut derived from the SAME final interpreter signature.
No prefix, lifecycle or output-law identity is supplied by the caller. -/
theorem actual_optional_identity_open_kernel_cut (owner : I) (ops : List (AsyncOperation I S Base))
    (opening : Base × S → PMF (Base × S)) (kernel : S → PMF S)
    (tail left : List (AsyncOperation I S Base))
    (hl : left = [] ∨ left = [.localStep owner (actorWordKernel [])])
    (hs : ownProtocolSignature owner ops = left ++ .interface owner opening :: .localStep owner kernel :: tail) :
    ∃ before gap later,
      ops = before ++ .interface owner opening :: (gap ++ .localStep owner kernel :: later) ∧
      (∀ op ∈ before, InteriorSafe owner op) ∧ (∀ op ∈ gap, SafeFor owner op) := by
  rcases hl with he | he
  · rw [he,List.nil_append] at hs
    exact actual_open_kernel_signature_cut owner ops opening kernel tail hs
  · rw [he,List.singleton_append] at hs
    obtain ⟨beforeIdentity,rest,hb,hbefore,hrest⟩ := signature_cons_extract owner ops _ _ hs
    obtain ⟨beforeOpen,gap,later,ho,hopen,hgap⟩ := actual_open_kernel_signature_cut owner rest opening kernel tail hrest
    refine ⟨beforeIdentity ++ [.localStep owner (actorWordKernel [])] ++ beforeOpen,gap,later,?_,?_,hgap⟩
    · rw [hb,ho]
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    · rw [interior_safe_append,interior_safe_append]
      refine ⟨⟨signature_nil_is_interior_safe owner beforeIdentity hbefore,?_⟩,hopen⟩
      intro op hm
      have he := List.mem_singleton.mp hm
      subst op; trivial

#print axioms actual_optional_identity_open_kernel_cut
end G1OwnOpeningKInputCut
