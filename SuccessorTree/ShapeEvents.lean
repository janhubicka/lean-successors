import SuccessorTree.ShapePreserving

/-!
# Intrinsic successor events

A shape map need not send the endpoint of a one-step transition to another
one-step endpoint; it may stretch that transition.  Nevertheless the first
target successor is uniquely determined by its mapped base, mapped parameter
list, and unchanged label.  It is this event, not the potentially stretched
endpoint node, that should represent a marked support occurrence in an
application such as the girth-five forest construction.
-/

namespace SuccessorTree

universe u v

/-- A named successor event, identified by its base, ordered parameter
list and label, together with the fact that this transition is legal. -/
structure IntrinsicEvent {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T] (S : STree T Label) where
  base : T
  params : List T
  label : Label
  has_child : ∃ b : T, S.succ base params label = some b

/-- A marked support occurrence keeps both its intrinsic event (which
fixes the label/port/projection role) and a possibly later history address
(which distinguishes copies after arbitrary shape-map stretching). -/
structure PointedOccurrence {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T] (S : STree T Label) where
  event : IntrinsicEvent S
  address : T
  event_below :
    ∃ b : T,
      S.succ event.base event.params event.label = some b ∧
        b ≤ address

namespace ShapeMap

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

/-- Transport the intrinsic event across a shape-preserving map.  The
weak-successor axiom ensures that the transported event is still legal. -/
def mapEvent (F : ShapeMap S) (e : IntrinsicEvent S) :
    IntrinsicEvent S where
  base := F e.base
  params := e.params.map F
  label := e.label
  has_child := by
    obtain ⟨b, hb⟩ := e.has_child
    obtain ⟨d, hd, _⟩ := F.weak_succ' hb
    exact ⟨d, hd⟩

@[simp] theorem mapEvent_base (F : ShapeMap S) (e : IntrinsicEvent S) :
    (F.mapEvent e).base = F e.base := rfl

@[simp] theorem mapEvent_params (F : ShapeMap S) (e : IntrinsicEvent S) :
    (F.mapEvent e).params = e.params.map F := rfl

@[simp] theorem mapEvent_label (F : ShapeMap S) (e : IntrinsicEvent S) :
    (F.mapEvent e).label = e.label := rfl

private theorem list_map_injective {α : Type u} {β : Type v}
    {f : α → β} (hf : Function.Injective f) :
    Function.Injective (List.map f) := by
  intro xs ys h
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.map_cons] at h
          have hp : f x = f y ∧ xs.map f = ys.map f :=
            List.cons.inj h
          have hxy : x = y := hf hp.1
          have hrest : xs = ys := ih hp.2
          subst y
          subst ys
          rfl

/-- Distinct intrinsic events remain distinct under any shape map, even
when the map stretches their terminal history nodes. -/
theorem mapEvent_injective (F : ShapeMap S) :
    Function.Injective (F.mapEvent) := by
  intro e e' h
  have hb : e.base = e'.base := by
    apply F.injective
    have hbase := congrArg (fun z : IntrinsicEvent S => z.base) h
    simpa only [mapEvent] using hbase
  have hp : e.params = e'.params := by
    apply list_map_injective F.injective
    have hparams := congrArg (fun z : IntrinsicEvent S => z.params) h
    simpa only [mapEvent] using hparams
  have hc : e.label = e'.label := by
    have hlabel := congrArg (fun z : IntrinsicEvent S => z.label) h
    simpa only [mapEvent] using hlabel
  cases e with
  | mk a p c ha =>
    cases e' with
    | mk b q d hb' =>
        dsimp at hb hp hc
        subst b
        subst q
        subst d
        rfl

/-- Transport the point together with its intrinsic role.  This is the
correct action on support-atom or principal-copy addresses under weak
successor preservation. -/
def mapPointed (F : ShapeMap S) (x : PointedOccurrence S) :
    PointedOccurrence S where
  event := F.mapEvent x.event
  address := F x.address
  event_below := by
    obtain ⟨b, hb, hba⟩ := x.event_below
    obtain ⟨d, hd, hdb⟩ := F.weak_succ' hb
    exact ⟨d, hd, hdb.trans (F.map_le_of_le hba)⟩

@[simp] theorem mapPointed_address (F : ShapeMap S)
    (x : PointedOccurrence S) :
    (F.mapPointed x).address = F x.address := rfl

@[simp] theorem mapPointed_event (F : ShapeMap S)
    (x : PointedOccurrence S) :
    (F.mapPointed x).event = F.mapEvent x.event := rfl

/-- Both the role and the address of a marked occurrence are retained
injectively by a shape map. -/
theorem mapPointed_injective (F : ShapeMap S) :
    Function.Injective (F.mapPointed) := by
  intro x y h
  have hev : x.event = y.event := by
    apply F.mapEvent_injective
    have hrole := congrArg (fun z : PointedOccurrence S => z.event) h
    simpa only [mapPointed] using hrole
  have haddr : x.address = y.address := by
    apply F.injective
    have hp := congrArg (fun z : PointedOccurrence S => z.address) h
    simpa only [mapPointed] using hp
  rcases x with ⟨ex, ax, hx⟩
  rcases y with ⟨ey, ay, hy⟩
  dsimp at hev haddr
  subst ey
  subst ay
  rfl

/-- Two copies of one marked occurrence are distinct as soon as their
history addresses are distinct, even if their transported intrinsic event
happens to coincide.  This is the separator needed for two-copy tests. -/
theorem mapPointed_ne_of_address_ne
    (F G : ShapeMap S) (x : PointedOccurrence S)
    (h : F x.address ≠ G x.address) :
    F.mapPointed x ≠ G.mapPointed x := by
  intro heq
  apply h
  have ha := congrArg (fun z : PointedOccurrence S => z.address) heq
  simpa only [mapPointed] using ha

end ShapeMap
end SuccessorTree
