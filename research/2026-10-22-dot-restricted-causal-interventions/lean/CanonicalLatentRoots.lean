import SelectedProfileSeparation

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No compilation, execution or verification certificate.
Concrete canonical hidden-root DAG and exact marked one-root projection.
The generic classical latent-projection theorem, finite counts and its use in
the original DAG/MAG/TCM endpoint are still separate full-claim obligations.
-/

namespace RestrictedCausal.LatentRoots

open SelectedWalk CanonicalSelection

universe u

structure MixedLaws {V : Type u} (G : MarkedGraph V) : Prop where
  symmetric : ∀ x y mx my, G.edge x y mx my → G.edge y x my mx
  irreflexive : ∀ x mx my, ¬ G.edge x x mx my
  no_tail_tail : ∀ x y, ¬ G.edge x y .tail .tail

def DirectedAcyclic {V : Type u} (G : MarkedGraph V) : Prop :=
  ∀ x xs, Route (Directed G) x xs x → xs = []

/-- Exactly one token per unordered bidirected edge, independent of any bows. -/
structure Root {V : Type u} [LinearOrder V] (G : MarkedGraph V) where
  «left» : V
  «right» : V
  ordered : «left» < «right»
  edge : G.edge «left» «right» .head .head

abbrev Vertex {V : Type u} [LinearOrder V] (G : MarkedGraph V) := Sum V (Root G)

def Incident {V : Type u} [LinearOrder V] {G : MarkedGraph V}
    (r : Root G) (x : V) : Prop := x = r.left ∨ x = r.right

def Arrow {V : Type u} [LinearOrder V] (G : MarkedGraph V) :
    Vertex G → Vertex G → Prop
  | .inl x, .inl y => Directed G x y
  | .inr r, .inl y => Incident r y
  | _, .inr _ => False

def dagGraph {V : Type u} [LinearOrder V] (G : MarkedGraph V) :
    MarkedGraph (Vertex G) where
  edge a b ma mb :=
    (Arrow G a b ∧ ma = .tail ∧ mb = .head) ∨
    (Arrow G b a ∧ ma = .head ∧ mb = .tail)

theorem no_root_parent {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (a : Vertex G) (r : Root G) : ¬ Arrow G a (.inr r) := by
  cases a <;> exact id

theorem root_route_trivial {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    {a b : Vertex G} {xs : List (Vertex G)} (h : Route (Arrow G) a xs b) :
    ∀ r, b = .inr r → a = .inr r ∧ xs = [] := by
  induction h with
  | nil a => exact fun r ha => ⟨ha, rfl⟩
  | @cons a b c xs hab hbc ih =>
      intro r hc
      obtain ⟨hb, _⟩ := ih r hc
      subst b
      exact (no_root_parent G a r hab).elim

/-- An observed-start directed route never visits a hidden root. Its entire
list is the image of a genuine directed route of G, not just a reachability bit. -/
theorem observed_route {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    {a b : Vertex G} {xs : List (Vertex G)} (h : Route (Arrow G) a xs b) :
    ∀ x, a = .inl x → ∃ y ys,
      b = .inl y ∧ xs = ys.map (fun z => Sum.inl z : V → Vertex G) ∧
      Route (Directed G) x ys y := by
  induction h with
  | nil a =>
      intro x ha
      exact ⟨x, [], ha, rfl, .nil x⟩
  | @cons a b c xs hab hbc ih =>
      intro x ha
      subst a
      cases b with
      | inl z =>
          obtain ⟨y, ys, hc, hxs, hp⟩ := ih z rfl
          exact ⟨y, z :: ys, hc, congrArg (List.cons (.inl z)) hxs, .cons hab hp⟩
      | inr r => exact hab.elim

theorem root_expansion_acyclic {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (hG : DirectedAcyclic G) (a : Vertex G) (xs : List (Vertex G))
    (h : Route (Arrow G) a xs a) : xs = [] := by
  cases a with
  | inr r => exact (root_route_trivial G h r rfl).2
  | inl x =>
      obtain ⟨y, ys, hxy, hxs, hp⟩ := observed_route G h x rfl
      have heq : x = y := Sum.inl.inj hxy
      subst y
      have hnil := hG x ys hp
      simpa only [hnil, List.map_nil] using hxs

theorem dag_directed_exact {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (a b : Vertex G) : Directed (dagGraph G) a b ↔ Arrow G a b := by
  change ((Arrow G a b ∧ _ ∧ _) ∨ (Arrow G b a ∧ _ ∧ _)) ↔ _
  simp

theorem dag_directed_acyclic {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (hG : DirectedAcyclic G) : DirectedAcyclic (dagGraph G) := by
  intro a xs h
  have hp := h.map id (fun a b hab => (dag_directed_exact G a b).mp hab)
  have hr : Route (Arrow G) a xs a := by simpa only [List.map_id] using hp
  exact root_expansion_acyclic G hG a xs hr

theorem retained_sink_stays_sink {V : Type u} [LinearOrder V]
    (G : MarkedGraph V) (s : V) (hs : ∀ v, ¬ Directed G s v)
    (b : Vertex G) : ¬ Arrow G (.inl s) b := by
  cases b with
  | inl v => exact hs v
  | inr r => exact id

/-- Add one genuinely exogenous indicator with exactly the named child. This
is a concrete source operation and does not delete the target's old parents. -/
def AddIndicator {V : Type u} (D : V → V → Prop) (target : V) :
    Option V → Option V → Prop
  | none, some y => y = target
  | some x, some y => D x y
  | _, none => False

theorem indicator_no_parent {V : Type u} (D : V → V → Prop) (target : V)
    (a : Option V) : ¬ AddIndicator D target a none := by
  cases a <;> exact id

theorem indicator_sole_child {V : Type u} (D : V → V → Prop) (target : V)
    (b : Option V) : AddIndicator D target none b ↔ b = some target := by
  cases b with
  | none => simp [AddIndicator]
  | some y => simp [AddIndicator]

theorem indicator_preserves_old_arrow {V : Type u} (D : V → V → Prop)
    (target x y : V) : AddIndicator D target (some x) (some y) ↔ D x y := Iff.rfl

theorem indicator_preserves_sink {V : Type u} (D : V → V → Prop)
    (target s : V) (hs : ∀ v, ¬ D s v) (b : Option V) :
    ¬ AddIndicator D target (some s) b := by
  cases b with
  | none => exact id
  | some v => exact hs v

theorem root_pair {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (laws : MixedLaws G) {x y : V} (hne : x ≠ y) {r : Root G}
    (hx : Incident r x) (hy : Incident r y) : G.edge x y .head .head := by
  rcases hx with rfl | rfl
  · rcases hy with rfl | rfl
    · exact (hne rfl).elim
    · exact r.edge
  · rcases hy with rfl | rfl
    · exact laws.symmetric _ _ _ _ r.edge
    · exact (hne rfl).elim

theorem bidirected_has_root {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (laws : MixedLaws G) {x y : V} (h : G.edge x y .head .head) :
    ∃ r : Root G, Incident r x ∧ Incident r y := by
  have hne : x ≠ y := by
    intro heq
    subst y
    exact laws.irreflexive x .head .head h
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · exact ⟨⟨x, y, hxy, h⟩, Or.inl rfl, Or.inr rfl⟩
  · exact ⟨⟨y, x, hyx, laws.symmetric _ _ _ _ h⟩, Or.inr rfl, Or.inl rfl⟩

/-- A retained adjacency or a noncollider path through one actual hidden root.
The longer-hidden-path exclusion is stated separately below, so this definition
is not claimed to be the general latent projection of an arbitrary DAG. -/
def RootProjection {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (x y : V) (mx my : Mark) : Prop :=
  x ≠ y ∧ ((dagGraph G).edge (.inl x) (.inl y) mx my ∨
    ∃ r : Root G,
      (dagGraph G).edge (.inl x) (.inr r) mx .tail ∧
      (dagGraph G).edge (.inr r) (.inl y) .tail my)

theorem no_root_adjacency {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (r s : Root G) (mr ms : Mark) :
    ¬ (dagGraph G).edge (.inr r) (.inr s) mr ms := by
  rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

theorem obs_root_marks {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (x : V) (r : Root G) (mx mr : Mark) :
    (dagGraph G).edge (.inl x) (.inr r) mx mr ↔
      Incident r x ∧ mx = .head ∧ mr = .tail := by
  change ((False ∧ _) ∨ (Incident r x ∧ _)) ↔ _
  simp

theorem root_obs_marks {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (r : Root G) (x : V) (mr mx : Mark) :
    (dagGraph G).edge (.inr r) (.inl x) mr mx ↔
      Incident r x ∧ mr = .tail ∧ mx = .head := by
  change ((Incident r x ∧ _) ∨ (False ∧ _)) ↔ _
  simp

theorem root_projection_exact {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (laws : MixedLaws G) (x y : V) (mx my : Mark) :
    RootProjection G x y mx my ↔ G.edge x y mx my := by
  constructor
  · rintro ⟨hne, hdir | ⟨r, hx, hy⟩⟩
    · rcases hdir with ⟨hxy, rfl, rfl⟩ | ⟨hyx, rfl, rfl⟩
      · exact hxy
      · exact laws.symmetric _ _ _ _ hyx
    · obtain ⟨hix, hmx, _⟩ := (obs_root_marks G x r mx .tail).mp hx
      obtain ⟨hiy, _, hmy⟩ := (root_obs_marks G r y .tail my).mp hy
      subst mx
      subst my
      exact root_pair G laws hne hix hiy
  · intro hedge
    have hne : x ≠ y := by
      intro heq
      subst y
      exact laws.irreflexive x mx my hedge
    refine ⟨hne, ?_⟩
    cases mx with
    | tail =>
        cases my with
        | tail => exact (laws.no_tail_tail x y hedge).elim
        | head => exact Or.inl (Or.inl ⟨hedge, rfl, rfl⟩)
    | head =>
        cases my with
        | tail => exact Or.inl (Or.inr ⟨laws.symmetric _ _ _ _ hedge, rfl, rfl⟩)
        | head =>
            obtain ⟨r, hx, hy⟩ := bidirected_has_root G laws hedge
            exact Or.inr ⟨r, Or.inr ⟨hx, rfl, rfl⟩, Or.inl ⟨hy, rfl, rfl⟩⟩

/-- General marked noncollider routes with the list of internal vertices.
Unlike RootProjection, this definition permits arbitrarily long interiors. -/
inductive NoncolliderRoute {V : Type u} (G : MarkedGraph V) :
    V → Mark → List V → V → Mark → Prop
  | single {a b ma mb} (edge : G.edge a b ma mb) :
      NoncolliderRoute G a ma [] b mb
  | step {a b c ma incoming outgoing mc mids}
      (edge : G.edge a b ma incoming)
      (active : ¬ (incoming = .head ∧ outgoing = .head))
      (tail : NoncolliderRoute G b outgoing mids c mc) :
      NoncolliderRoute G a ma (b :: mids) c mc

/-- A latent-interior noncollider path test, without an a priori interior bound. -/
def LatentPathProjection {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (x y : V) (mx my : Mark) : Prop :=
  x ≠ y ∧ ∃ roots : List (Root G),
    NoncolliderRoute (dagGraph G) (.inl x) mx
      (roots.map (fun r => Sum.inr r : Root G → Vertex G)) (.inl y) my

/-- Longer hidden interiors are excluded by actual absence of root-root
adjacency. The forward proof does not assume the desired two-edge form. -/
theorem latent_path_projection_iff {V : Type u} [LinearOrder V]
    (G : MarkedGraph V) (x y : V) (mx my : Mark) :
    LatentPathProjection G x y mx my ↔ RootProjection G x y mx my := by
  constructor
  · rintro ⟨hne, roots, h⟩
    refine ⟨hne, ?_⟩
    cases roots with
    | nil =>
        cases h with
        | single hedge => exact Or.inl hedge
    | cons r rs =>
        cases h with
        | @step _ _ _ _ incoming outgoing _ _ hfirst hn htail =>
            cases rs with
            | nil =>
                cases htail with
                | single hlast =>
                    have hi := ((obs_root_marks G x r mx incoming).mp hfirst).2.2
                    have ho := ((root_obs_marks G r y outgoing my).mp hlast).2.1
                    subst incoming
                    subst outgoing
                    exact Or.inr ⟨r, hfirst, hlast⟩
            | cons s rest =>
                cases htail with
                | step hmid _ _ => exact (no_root_adjacency G r s _ _ hmid).elim
  · rintro ⟨hne, hedge | ⟨r, hfirst, hlast⟩⟩
    · exact ⟨hne, [], .single hedge⟩
    · refine ⟨hne, [r], .step hfirst ?_ (.single hlast)⟩
      intro hbad
      exact Mark.noConfusion hbad.1

theorem latent_path_projection_exact {V : Type u} [LinearOrder V]
    (G : MarkedGraph V) (laws : MixedLaws G) (x y : V) (mx my : Mark) :
    LatentPathProjection G x y mx my ↔ G.edge x y mx my :=
  (latent_path_projection_iff G x y mx my).trans (root_projection_exact G laws x y mx my)

end RestrictedCausal.LatentRoots

namespace RestrictedCausal.SourceSelection

open SelectedWalk CanonicalSelection

universe u v

theorem directed_route_shape {X : Type u} {S : Type v} (H : SelectedGraph X S)
    {a b : Sum X S} {xs : List (Sum X S)}
    (h : Route (Directed (graph H)) a xs b) :
    ∀ y : X, b = .inl y → ∃ x ys,
      a = .inl x ∧ xs = ys.map (fun z => Sum.inl z : X → Sum X S) ∧
      Route (Directed H.observed) x ys y := by
  induction h with
  | nil a =>
      intro y ha
      exact ⟨y, [], ha, rfl, .nil y⟩
  | @cons a b c xs hab hbc ih =>
      intro y hc
      obtain ⟨z, zs, hb, hxs, hp⟩ := ih y hc
      subst b
      cases a with
      | inl x =>
          exact ⟨x, z :: zs, rfl, congrArg (List.cons (.inl z)) hxs, .cons hab hp⟩
      | inr s => exact (no_selected_departure H s (.inl z) hab).elim

theorem selected_directed_acyclic {X : Type u} {S : Type v} (H : SelectedGraph X S)
    (hH : LatentRoots.DirectedAcyclic H.observed) :
    LatentRoots.DirectedAcyclic (graph H) := by
  intro a xs h
  cases a with
  | inl x =>
      obtain ⟨z, zs, hxz, hxs, hp⟩ := directed_route_shape H h x rfl
      have heq : x = z := Sum.inl.inj hxz
      subst z
      have hz := hH x zs hp
      simpa only [hz, List.map_nil] using hxs
  | inr s =>
      cases h with
      | nil => rfl
      | cons hstep _ => exact (no_selected_departure H s _ hstep).elim

theorem canonical_mixed_laws {X : Type u} [LinearOrder X] (Q : Profile X)
    (laws : LatentRoots.MixedLaws Q.observed) :
    LatentRoots.MixedLaws (graph (canonical Q)) := by
  constructor
  · intro a b ma mb h
    cases a with
    | inl x =>
        cases b with
        | inl y => exact laws.symmetric x y ma mb h
        | inr s => exact h
    | inr s =>
        cases b with
        | inl y => exact h
        | inr t => exact h.1.elim
  · intro a ma mb h
    cases a with
    | inl x => exact laws.irreflexive x ma mb h
    | inr s => exact h.1.elim
  · intro a b h
    cases a with
    | inl x =>
        cases b with
        | inl y => exact laws.no_tail_tail x y h
        | inr s => exact Mark.noConfusion h.2
    | inr s =>
        cases b with
        | inl y => exact Mark.noConfusion h.2
        | inr t => exact h.1.elim

end RestrictedCausal.SourceSelection
