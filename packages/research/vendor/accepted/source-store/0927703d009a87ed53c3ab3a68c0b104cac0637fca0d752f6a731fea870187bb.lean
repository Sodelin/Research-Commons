import UnifiedLean.Source.E8SCFG2RootEventDecoder
import E8SCFG2ProviderBoundaryContract

/-!
# Fixed-scaffold BE ownership from literal endpoint origins

The guards record source assignments/checks at public PKProbDesign/CParty
27afdd054272dbda8a74c8aad156970a44c23cd8, generate_exact_basic.hh673--853 and
wmb_geometry.hh73--86,132--148,170--180. They do NOT assume the desired
all-BE-descendant ownership conclusion. The unchecked same-anchor BE base is
safe for this invariant only after ownership has propagated from its caller.

This source-schema theorem still needs actual generated/executed-tree
refinement and the validated context partner relation's equivalence to paper G.
It is not canonical RNA, density, energy, rendering or probability correctness.
-/
noncomputable section
open scoped Classical
namespace UnifiedLean.Source.E8SCFG2BEOwnership
open E8SCFG2RuntimeChildAdapter E8SCFG2ProviderBoundaryContract
open UnifiedLean.Source.E8SCFG2RootEventDecoder

/-- Matches is_fixed_scaffold_pair's two directional partner tests; no
involution is silently assumed for an arbitrary context function. -/
def PartnerPair (partner : ℤ → ℤ) (i j : ℤ) : Prop :=
  partner i = j ∨ partner j = i

def OwnedIfBE (partner : ℤ → ℤ) (key : ItemKey) : Prop :=
  key.nonterminal = .BE → PartnerPair partner key.i key.j ∧ PartnerPair partner key.ip key.jp

/-- Literal checked/assigned endpoints, separate from the numerical
SourceGuard. Values not used by a rule are not constrained artificially. -/
def OriginGuard (partner : ℤ → ℤ) (p : ItemKey) (r : RuleId) (s : RuleSplit) : Prop :=
  match r with
  | .BE_STACK => partner (p.i+1) = p.j-1
  | .BE_INTERNAL_LOOP | .BE_WIP_WIP | .BE_WIP_BASEPAIR | .BE_BASEPAIR_WIP => s.l = partner s.k
  | .WMBP_SPLIT_BE_WMBP_VP | .WMBP_SPLIT_BE_WMBW_VP => s.p = partner s.q
  | .WMBP_SPLIT_BE_WI_VP => s.l = partner s.k
  | .WMB_SPLIT_BE_WMBP_WI => s.p = partner p.j ∧ s.q = partner s.l
  | _ => True

private theorem raw_child_owned (partner : ℤ → ℤ) (p : ItemKey)
    (r : RuleId) (s : RuleSplit) (hf : RuleFamily r p.nonterminal)
    (ho : OriginGuard partner p r s) (hp : OwnedIfBE partner p)
    (c : ItemKey) (hc : c ∈ sourceChildren partner p r s) : OwnedIfBE partner c := by
  by_cases hparent : p.nonterminal = .BE
  · have hparentOwned := hp hparent
    clear hp
    cases r <;>
      simp_all [sourceChildren, OriginGuard, RuleFamily, prefixSpan, optionalSpan,
        OwnedIfBE, PartnerPair, primary, band, recursiveVP, List.mem_append, List.mem_cons, List.mem_singleton]
    all_goals
      repeat' first
      | split at hc
      | (rcases hc with hc | hc)
      | (rcases hc with ⟨h,hc⟩)
      | subst c
    all_goals try simp_all [primary, band, recursiveVP, OwnedIfBE, PartnerPair]
    all_goals aesop
  · cases r <;>
      simp_all [sourceChildren, OriginGuard, RuleFamily, prefixSpan, optionalSpan,
        OwnedIfBE, PartnerPair, primary, band, recursiveVP, List.mem_append, List.mem_cons, List.mem_singleton]
    all_goals
      repeat' first
      | split at hc
      | (rcases hc with hc | hc)
      | (rcases hc with ⟨h,hc⟩)
      | subst c
    all_goals try simp_all [primary, band, recursiveVP, OwnedIfBE, PartnerPair]
    all_goals aesop

/-- Child normalization cannot create BE from the VP_DIRECT alias. For BE
it leaves every coordinate and both ownership tests unchanged. -/
theorem forward_key_owned (partner : ℤ → ℤ) (r : RuleId) (c : ItemKey)
    (h : OwnedIfBE partner c) : OwnedIfBE partner (forwardChildKey r c) := by
  by_cases ha : aliasesDirect r c
  · simp [forwardChildKey, ha, OwnedIfBE]
  · simpa [forwardChildKey, ha] using h

/-- All57 normalized-child schemas preserve the invariant under primitive
endpoint-origin facts and an owned BE caller, if the caller is BE. -/
theorem normalized_child_owned (partner : ℤ → ℤ) (p : ItemKey)
    (r : RuleId) (s : RuleSplit) (hf : RuleFamily r p.nonterminal)
    (ho : OriginGuard partner p r s) (hp : OwnedIfBE partner p)
    (c : ItemKey) (hc : c ∈ normalizedChildren partner p r s) : OwnedIfBE partner c := by
  obtain ⟨raw,hm,rfl⟩ := List.mem_map.mp hc
  exact forward_key_owned partner r raw (raw_child_owned partner p r s hf ho hp raw hm)

/-- Every node satisfies its local endpoint assignments. Actual factory
membership is still a distinct execution/generated-list admission, not this
recursive certificate or an arbitrary asserted whole-tree ownership field. -/
def OriginsCompatible (partner : ℤ → ℤ) {key : ItemKey} (tree : SchemaTree partner key) : Prop := by
  induction tree with
  | @node key rule split _ _ _ _ ih =>
    exact OriginGuard partner key rule split ∧ ∀ idx, ih idx

/-- All node ownership, used to distinguish a root test from a whole-tree
invariant. It is a conclusion below, not an origin-certificate field. -/
def AllBEOwned (partner : ℤ → ℤ) {key : ItemKey} (tree : SchemaTree partner key) : Prop := by
  induction tree with
  | @node key _ _ _ _ _ _ ih =>
    exact OwnedIfBE partner key ∧ ∀ idx, ih idx

theorem tree_owned_from_origins (partner : ℤ → ℤ) {key : ItemKey}
    (tree : SchemaTree partner key) :
    OwnedIfBE partner key → OriginsCompatible partner tree → AllBEOwned partner tree := by
  induction tree with
  | @node key rule split hv hf hg children ih =>
    intro hp ho
    change OriginGuard partner key rule split ∧ (∀ idx, OriginsCompatible partner (children idx)) at ho
    change OwnedIfBE partner key ∧ (∀ idx, AllBEOwned partner (children idx))
    refine ⟨hp,?_⟩
    intro idx
    apply ih idx _ (ho.2 idx)
    exact normalized_child_owned partner key rule split hf ho.1 hp
      ((normalizedChildren partner key rule split).get idx) (List.get_mem _ idx)

/-- The actual ROOT family W is not BE. Ownership therefore propagates from
local endpoint origins to every BE node, including same-anchor base leaves. -/
theorem root_tree_be_owned (partner : ℤ → ℤ) (n : ℕ)
    (tree : SchemaTree partner (rootKey n)) (ho : OriginsCompatible partner tree) :
    AllBEOwned partner tree := by
  apply tree_owned_from_origins partner tree _ ho
  simp [OwnedIfBE, rootKey]

#print axioms forward_key_owned
#print axioms normalized_child_owned
#print axioms tree_owned_from_origins
#print axioms root_tree_be_owned
end UnifiedLean.Source.E8SCFG2BEOwnership
