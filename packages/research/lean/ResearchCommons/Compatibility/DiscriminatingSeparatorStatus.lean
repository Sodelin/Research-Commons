import CommonObservedMAG

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Classical shared-separator argument, as in the discussion proving
Ali--Richardson--Spirtes (2009), Lemma 3.9. The complete MEC criterion is
Spirtes--Richardson (1997), restated there as Theorem 4.1, not Theorem 3.7.
The latter and the full selected-MAG separation representation remain
separate formal dependencies. No equivalence theorem is postulated below.

The prefix carries actual incidences: every internal prefix vertex is a
collider and a parent of the terminal y. Its last vertex b is deliberately
excluded from that requirement. The original full simple-path list is kept
when testing each shortened prefix, so no active-walk theorem for graphs
with undirected edges is assumed.
-/

namespace RestrictedCausal.DiscriminatingStatus

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation
open SourceSelection (AncestorOf)

universe u

def ColliderParentStep {V : Type u} (G : MarkedGraph V) (y : V)
    (p q : Arrival V) : Prop :=
  ∃ outgoing incoming, G.edge p.vertex q.vertex outgoing incoming ∧
    q.incoming = some incoming ∧
    (match p.incoming with
    | none => True
    | some previous => previous = .head ∧ outgoing = .head ∧ Directed G p.vertex y)

/-- Delete a middle block, retaining the whole initial prefix and terminal.
The resulting vertex list is literally a sublist of the full simple path. -/
theorem prefix_terminal_nodup {V : Type u} («prefix» middle : List V) (y : V)
    (h : («prefix» ++ middle ++ [y]).Nodup) : («prefix» ++ [y]).Nodup := by
  refine List.Nodup.sublist ?_ h
  simpa only [List.append_assoc] using (List.sublist_append_right middle [y]).append_left «prefix»

theorem conditioned_ancestor {V : Type u} (G : MarkedGraph V) (Z : V → Prop)
    (v : V) (hv : Z v) : AncestorOf G Z v := ⟨v, ⟨[], .nil _⟩, hv⟩

/-- Every internal collider-parent must lie in a separating set. Otherwise
the active accumulated prefix followed by its actual arrow to y is a simple
active path. The next collider is then activated by membership in Z itself. -/
theorem collider_parent_prefix_activated {V : Type u} (G : MarkedGraph V)
    (Z : V → Prop) (x y : V)
    {p q : Arrival V} {xs : List (Arrival V)}
    (h : Route (ColliderParentStep G y) p xs q)
    («prefix» : List (Arrival V))
    (hp : Route (RealStep G Z) ⟨x, none⟩ «prefix» p)
    (hnd : ((((⟨x, none⟩ :: «prefix») ++ xs).map Arrival.vertex) ++ [y]).Nodup)
    (hsep : ¬ ActiveConnection G Z x y) : Route (RealStep G Z) p xs q := by
  revert hp hnd
  revert «prefix»
  induction h with
  | nil p => intro _ _ _; exact .nil _
  | @cons p «next» q rest hstep hrest ih =>
      intro «prefix» hp hnd
      obtain ⟨outgoing, incoming, hedge, hmark, hcollider⟩ := hstep
      have active : DepartureAllowed Z (AncestorOf G Z) p.vertex p.incoming outgoing := by
        cases hm : p.incoming with
        | none => trivial
        | some previous =>
            have triple : previous = .head ∧ outgoing = .head ∧ Directed G p.vertex y := by
              simpa only [hm] using hcollider
            have hz : Z p.vertex := by
              by_contra hn
              have last : RealStep G Z p ⟨y, some .head⟩ := by
                refine ⟨.tail, .head, triple.2.2, rfl, ?_⟩
                simpa [hm, ActiveAt] using hn
              have whole := hp.append (.cons last (.nil _))
              have nd : ((((⟨x, none⟩ :: «prefix»).map Arrival.vertex)) ++ [y]).Nodup := by
                apply prefix_terminal_nodup _ ((«next» :: rest).map Arrival.vertex) y
                simpa only [List.map_append, List.append_assoc] using hnd
              apply hsep
              refine ⟨some .head, «prefix» ++ [⟨y, some .head⟩], whole, ?_⟩
              simpa only [List.map_cons, List.map_append, List.map_nil, List.cons_append] using nd
            have ha := conditioned_ancestor G Z p.vertex hz
            simpa [DepartureAllowed, hm, triple.1, triple.2.1, ActiveAt] using ha
      have copied : RealStep G Z p «next» := ⟨outgoing, incoming, hedge, hmark, active⟩
      refine .cons copied (ih («prefix» ++ [«next»]) (hp.append (.cons copied (.nil _))) ?_)
      simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using hnd

def TerminalCollider {V : Type u} (p : Arrival V) (outgoing : Mark) : Prop :=
  p.incoming = some .head ∧ outgoing = .head

theorem terminal_if_conditioned_collider {V : Type u} (G : MarkedGraph V)
    (Z : V → Prop) (p : Arrival V) (outgoing : Mark)
    (hc : TerminalCollider p outgoing) (hz : Z p.vertex) :
    DepartureAllowed Z (AncestorOf G Z) p.vertex p.incoming outgoing := by
  obtain ⟨hin, hout⟩ := hc
  simpa [DepartureAllowed, hin, hout, ActiveAt] using conditioned_ancestor G Z p.vertex hz

theorem terminal_if_unconditioned_noncollider {V : Type u} (G : MarkedGraph V)
    (Z : V → Prop) (p : Arrival V) (outgoing : Mark)
    (hc : ¬ TerminalCollider p outgoing) (hz : ¬ Z p.vertex) :
    DepartureAllowed Z (AncestorOf G Z) p.vertex p.incoming outgoing := by
  cases hm : p.incoming with
  | none => trivial
  | some previous =>
      have hn : ¬ (previous = .head ∧ outgoing = .head) := by
        rintro ⟨rfl, hout⟩
        exact hc ⟨hm, hout⟩
      simpa only [DepartureAllowed, hm, ActiveAt, if_neg hn] using hz

/-- The terminal triple's status is determined by any one valid separator.
This includes the unshielded length-two case (empty collider-parent interior).
For a genuine discriminating path its interior is nonempty and x,y are
nonadjacent; those additional properties are not needed for this implication.
The displayed separator is actual m-separation under the route definition. -/
theorem terminal_collider_iff_not_mem {V : Type u} (G : MarkedGraph V)
    (Z : V → Prop) (x y : V) {b : Arrival V} {xs : List (Arrival V)}
    («prefix» : Route (ColliderParentStep G y) ⟨x, none⟩ xs b)
    (outgoing incoming : Mark) (last : G.edge b.vertex y outgoing incoming)
    (hnd : (((⟨x, none⟩ :: xs).map Arrival.vertex) ++ [y]).Nodup)
    (hsep : ¬ ActiveConnection G Z x y) : TerminalCollider b outgoing ↔ ¬ Z b.vertex := by
  classical
  have activePrefix := collider_parent_prefix_activated G Z x y «prefix» [] (.nil _) hnd hsep
  have blocked : ¬ DepartureAllowed Z (AncestorOf G Z) b.vertex b.incoming outgoing := by
    intro hdeparture
    have edge : RealStep G Z b ⟨y, some incoming⟩ := ⟨outgoing, incoming, last, rfl, hdeparture⟩
    apply hsep
    refine ⟨some incoming, xs ++ [⟨y, some incoming⟩], activePrefix.append (.cons edge (.nil _)), ?_⟩
    simpa only [List.map_cons, List.map_append, List.map_nil, List.cons_append] using hnd
  constructor
  · intro hc hz
    exact blocked (terminal_if_conditioned_collider G Z b outgoing hc hz)
  · intro hn
    by_contra hc
    exact blocked (terminal_if_unconditioned_noncollider G Z b outgoing hc hn)

/-- A single shared separating set determines the discriminated status in
both graphs. The prefixes may have different chosen edge marks but the same
terminal vertex b. There is no assertion that all discriminating paths of
one graph also occur in the other. -/
theorem shared_separator_terminal_agreement {V : Type u} (G H : MarkedGraph V)
    (Z : V → Prop) (x y b : V)
    {p q : Arrival V} {xs ys : List (Arrival V)} (hp : p.vertex = b) (hq : q.vertex = b)
    (prefixG : Route (ColliderParentStep G y) ⟨x, none⟩ xs p)
    (prefixH : Route (ColliderParentStep H y) ⟨x, none⟩ ys q)
    (outG inG outH inH : Mark)
    (lastG : G.edge p.vertex y outG inG) (lastH : H.edge q.vertex y outH inH)
    (simpleG : (((⟨x, none⟩ :: xs).map Arrival.vertex) ++ [y]).Nodup)
    (simpleH : (((⟨x, none⟩ :: ys).map Arrival.vertex) ++ [y]).Nodup)
    (sepG : ¬ ActiveConnection G Z x y) (sepH : ¬ ActiveConnection H Z x y) :
    TerminalCollider p outG ↔ TerminalCollider q outH := by
  have hG := terminal_collider_iff_not_mem G Z x y prefixG outG inG lastG simpleG sepG
  have hH := terminal_collider_iff_not_mem H Z x y prefixH outH inH lastH simpleH sepH
  have same : (¬ Z p.vertex) ↔ ¬ Z q.vertex := by rw [hp, hq]
  exact hG.trans (same.trans hH.symm)

def Adjacent {V : Type u} (G : MarkedGraph V) (x y : V) : Prop :=
  ∃ mx my, G.edge x y mx my

def SingleEdges {V : Type u} (G : MarkedGraph V) : Prop :=
  ∀ x y mx my nx ny, G.edge x y mx my → G.edge x y nx ny → mx = nx ∧ my = ny

def Collider {V : Type u} (G : MarkedGraph V) (a b c : V) : Prop :=
  ∃ ma mc, G.edge a b ma .head ∧ G.edge b c .head mc

theorem collider_iff_chosen_marks {V : Type u} (G : MarkedGraph V) (single : SingleEdges G)
    (a b c : V) (ma mb nb nc : Mark)
    («first» : G.edge a b ma mb) (last : G.edge b c nb nc) :
    Collider G a b c ↔ mb = .head ∧ nb = .head := by
  constructor
  · rintro ⟨ma', mc', first', last'⟩
    exact ⟨(single a b ma mb ma' .head «first» first').2,
      (single b c nb nc .head mc' last last').1⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨ma, nc, «first», last⟩

theorem collider_iff_not_mem_separator {V : Type u} (G : MarkedGraph V)
    (single : SingleEdges G) (Z : V → Prop) (x b y : V)
    («first» : Adjacent G x b) (last : Adjacent G b y)
    (simple : ([x, b, y] : List V).Nodup) (sep : ¬ ActiveConnection G Z x y) :
    Collider G x b y ↔ ¬ Z b := by
  obtain ⟨mx, mb, «first»⟩ := «first»
  obtain ⟨nb, ny, last⟩ := last
  have «prefix» : Route (ColliderParentStep G y) ⟨x, none⟩ [⟨b, some mb⟩] ⟨b, some mb⟩ :=
    .cons ⟨mx, mb, «first», rfl, trivial⟩ (.nil _)
  have h := terminal_collider_iff_not_mem G Z x y «prefix» nb ny last simple sep
  have marks : (mb = .head ∧ nb = .head) ↔ TerminalCollider (⟨b, some mb⟩ : Arrival V) nb := by
    simp only [TerminalCollider, Option.some.injEq]
  exact (collider_iff_chosen_marks G single x b y mx mb nb ny «first» last).trans (marks.trans h)

def SharedSeparators {V : Type u} (G H : MarkedGraph V) : Prop :=
  ∀ x y, x ≠ y → ¬ Adjacent G x y → ∃ Z : V → Prop,
    ¬ Z x ∧ ¬ Z y ∧ ¬ ActiveConnection G Z x y ∧ ¬ ActiveConnection H Z x y

theorem shared_separators_unshielded {V : Type u} (G H : MarkedGraph V)
    (singleG : SingleEdges G) (singleH : SingleEdges H)
    (skeleton : ∀ x y, Adjacent G x y ↔ Adjacent H x y)
    (shared : SharedSeparators G H) (x b y : V) (hxy : x ≠ y)
    («first» : Adjacent G x b) (last : Adjacent G b y) (nonedge : ¬ Adjacent G x y)
    (simple : ([x, b, y] : List V).Nodup) : Collider G x b y ↔ Collider H x b y := by
  obtain ⟨Z, _, _, sepG, sepH⟩ := shared x y hxy nonedge
  exact (collider_iff_not_mem_separator G singleG Z x b y «first» last simple sepG).trans
    (collider_iff_not_mem_separator H singleH Z x b y ((skeleton x b).mp «first»)
      ((skeleton b y).mp last) simple sepH).symm

end RestrictedCausal.DiscriminatingStatus

namespace RestrictedCausal.HPLTarget

open SelectedWalk OriginalProjection DiscriminatingStatus

universe u v w

theorem endpoint_mark_unique {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (m n : Mark)
    (hm : EndpointMark D x y m) (hn : EndpointMark D x y n) : m = n := by
  cases m <;> cases n
  · rfl
  · exact ((endpoint_head_iff D x y).mp hn ((endpoint_tail_iff D x y).mp hm)).elim
  · exact ((endpoint_head_iff D x y).mp hm ((endpoint_tail_iff D x y).mp hn)).elim
  · rfl

theorem mag_single_edges {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) : SingleEdges (mag D) := by
  intro x y mx my nx ny hm hn
  exact ⟨endpoint_mark_unique D x y mx nx hm.2.1 hn.2.1,
    endpoint_mark_unique D y x my ny hm.2.2 hn.2.2⟩

end RestrictedCausal.HPLTarget
