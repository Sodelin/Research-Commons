import UnifiedLean.Source.E8SCFG2RootEventDecoder

/-!
# Exact normalized root carrier excludes auxiliary VP chart families

Pinned public TakumiOtagaki/PKProbDesign27af child expansion plus runtime
WMBP_DIRECT_VP alias. VP_CLOSED is produced only by a VP_CLOSED caller;
VP_DIRECT's sole external introduction is normalized to public VP.
This is a root schema invariant, not raw all-chart support equality or
an executed C++ tree admission. In particular the weaker auxiliary closed
endpoint guard does not by itself witness a root-live RNA defect.
-/
noncomputable section
open scoped Classical
namespace UnifiedLean.Source.E8SCFG2RootCarrier
open E8SCFG2RuntimeChildAdapter E8SCFG2ProviderBoundaryContract
open UnifiedLean.Source.E8SCFG2RootEventDecoder
open UnifiedLean.Source.E8PaperGammaAdmission

def RootFamily (nt : NonTerminal) : Prop := nt ≠ .VP_CLOSED ∧ nt ≠ .VP_DIRECT

/-- Literal57-schema/root-runtime preservation. The WMBP direct child is
normalized before this conclusion; raw-child exclusion would be false. -/
theorem normalized_child_root_family (partner : ℤ → ℤ) (p : ItemKey)
    (r : RuleId) (s : RuleSplit) (hf : RuleFamily r p.nonterminal)
    (hp : RootFamily p.nonterminal) (c : ItemKey)
    (hc : c ∈ normalizedChildren partner p r s) : RootFamily c.nonterminal := by
  obtain ⟨raw,hm,rfl⟩ := List.mem_map.mp hc
  cases r <;>
    simp_all [sourceChildren,RuleFamily,prefixSpan,optionalSpan,
      RootFamily,recursiveVP,List.mem_append,List.mem_cons]
  all_goals
    repeat' first
    | split at hm
    | (rcases hm with hm | hm)
    | (rcases hm with ⟨h,hm⟩)
    | subst raw
  all_goals simp_all [forwardChildKey,aliasesDirect,primary,band]

/-- All decoded parent events retain the root's actual permitted carrier;
no auxiliary-family absence is a whole-stream premise. -/
theorem bounded_events_root_family (partner : ℤ → ℤ) (n : ℕ) {key : ItemKey}
    (tree : SchemaTree partner key) :
    RootFamily key.nonterminal → ∀ hupper : key.j ≤ (n : ℤ),
      ∀ e ∈ boundedEvents partner n tree hupper, RootFamily e.family := by
  induction tree with
  | @node key rule split hv hf hg children ih =>
    intro hp hupper e he
    change e ∈ eventFromKey n key hv hupper ::
      (List.ofFn (fun idx => boundedEvents partner n (children idx)
        (child_upper_from_local_guard partner n key rule split hf hg hupper idx))).flatten at he
    rcases List.mem_cons.mp he with he | he
    · subst e
      exact hp
    · obtain ⟨childEvents,hm,he⟩ := List.mem_flatten.mp he
      obtain ⟨idx,rfl⟩ := List.mem_ofFn.mp hm
      apply ih idx _ _ e he
      exact normalized_child_root_family partner key rule split hf hp
        ((normalizedChildren partner key rule split).get idx) (List.get_mem _ idx)

theorem root_events_exclude_auxiliary (partner : ℤ → ℤ) (n : ℕ)
    (tree : SchemaTree partner (rootKey n)) (e : SourceEvent n)
    (he : e ∈ rootEvents partner n tree) :
    e.family ≠ .VP_CLOSED ∧ e.family ≠ .VP_DIRECT := by
  apply bounded_events_root_family partner n tree _ _ e he
  simp [RootFamily,rootKey]

#print axioms normalized_child_root_family
#print axioms bounded_events_root_family
#print axioms root_events_exclude_auxiliary
end UnifiedLean.Source.E8SCFG2RootCarrier
