import G1ActualOriginalPrivateAsyncStep

/-! A finite independent coordinate tensor has a concrete AsyncOperation
serialization. Every distinct actor is sampled once from its own actual
input coordinate, followed by the base. This is the finite PMF algebra
needed to bind the actual source epoch tensor, not a source independence
assumption or a replacement of the source calendar. -/
namespace G1FiniteAsyncCoordinateDraw
set_option backward.isDefEq.respectTransparency false
open G1PendingActorInterfaceCommutation G1ActualJointEpoch G1ActualJointProgram
open scoped Classical
universe u v
variable {I : Type u} {S : Type v} {Base : Type v} [DecidableEq I]

abbrev ActorDrawData (S : Type v) (Base : Type v) : List I → Type v
  | [] => Base
  | _::actors => S × ActorDrawData S Base actors

noncomputable def frozenDrawProduct (laws : I → PMF S) (base : PMF Base) :
    (actors : List I) → PMF (ActorDrawData S Base actors)
  | [] => base
  | actor::actors => independentProduct (laws actor) (frozenDrawProduct laws base actors)

noncomputable def installFrozenDraw (slots : I → S) :
    (actors : List I) → ActorDrawData S Base actors → Base × (I → S)
  | [],base => (base,slots)
  | actor::actors,data => installFrozenDraw (Function.update slots actor data.1) actors data.2

def actorDrawValues (values : I → S) (base : Base) :
    (actors : List I) → ActorDrawData S Base actors
  | [] => base
  | actor::actors => (values actor,actorDrawValues values base actors)

lemma install_actual_coordinate_values (slots values : I → S) (base : Base) (actors : List I) :
    installFrozenDraw slots actors (actorDrawValues values base actors) =
      (base,fun actor => if actor ∈ actors then values actor else slots actor) := by
  induction actors generalizing slots with
  | nil => simp [installFrozenDraw,actorDrawValues]
  | cons actor actors ih =>
    simp only [actorDrawValues,installFrozenDraw,ih]
    congr 1
    funext other
    by_cases hm : other ∈ actors <;> by_cases he : other = actor <;>
      simp [List.mem_cons,hm,he]

omit [DecidableEq I] in
lemma frozen_draw_product_congr (actors : List I) (left right : I → PMF S) (base : PMF Base)
    (h : ∀ actor ∈ actors, left actor = right actor) :
    frozenDrawProduct left base actors = frozenDrawProduct right base actors := by
  induction actors with
  | nil => rfl
  | cons actor actors ih =>
    simp only [frozenDrawProduct,h actor (List.mem_cons_self)]
    rw [ih (fun other hm => h other (List.mem_cons_of_mem actor hm))]

/-- The full finite actor/base tensor is serialized by actual local updates
without resampling another actor's input or changing inactive coordinates. -/
theorem finite_tensor_is_serial_async_program (actors : List I) (hn : actors.Nodup)
    (rows : I → S → PMF S) (base : Base → PMF Base) (initial : Base × (I → S)) :
    asyncProgram (actors.map (fun actor => AsyncOperation.localStep actor (rows actor)) ++
        [AsyncOperation.exterior base]) initial =
      (frozenDrawProduct (fun actor => rows actor (initial.2 actor)) (base initial.1) actors).map
        (installFrozenDraw initial.2 actors) := by
  induction actors generalizing initial with
  | nil => simp [asyncProgram,asyncStep,frozenDrawProduct,installFrozenDraw]
  | cons actor actors ih =>
    have hp := List.nodup_cons.mp hn
    simp only [List.map_cons,List.cons_append,asyncProgram,asyncStep,PMF.bind_map,Function.comp_def,
      frozenDrawProduct,independentProduct,PMF.map_bind,PMF.map_comp]
    congr 1
    funext value
    rw [ih hp.2]
    have ht : frozenDrawProduct (fun other => rows other (Function.update initial.2 actor value other))
        (base initial.1) actors =
      frozenDrawProduct (fun other => rows other (initial.2 other)) (base initial.1) actors := by
      apply frozen_draw_product_congr
      intro other hm
      have hne : other ≠ actor := by
        intro he
        exact hp.1 (by simpa only [he] using hm)
      rw [Function.update_of_ne hne]
    rw [ht]
    rfl

#print axioms finite_tensor_is_serial_async_program
end G1FiniteAsyncCoordinateDraw
