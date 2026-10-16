import SuccessorTree.Counterexample.RootMarkerRigidity
import Mathlib.Tactic

/-!
# Root-marker transport through pure shape-preserving maps

A weak successor with exactly the original root as its ancestral
parameter is carried by any map fixing that root to another such
outgoing successor, *regardless of how many intermediate target
levels that shape map inserts*.

This is the key reason the counterexample's root marker survives
outer pure maps, without requiring any direct A.3(2) property.
-/

namespace SuccessorTree.FreeAncestral

/-- A root marker remains visible on all extensions of a marked node. -/
theorem HasRootMarkerAt.mono
    {x y : Node Unit 1} {m : Nat}
    (hxy : x ≤ y) (h : HasRootMarkerAt x m) :
    HasRootMarkerAt y m := by
  obtain ⟨z, hzx, hzlev, hzcode⟩ := h
  exact ⟨z, hzx.trans hxy, hzlev, hzcode⟩

/-- Any mapped free successor whose only parameter is the fixed
root still has the root marker in its canonical intrinsic code. -/
theorem image_root_successor_has_marker
    (H : ShapeMap (freeSTree (Label := Unit) (arity := 1)))
    (hroot : H (rootNode (Label := Unit) (arity := 1)) =
      rootNode (Label := Unit) (arity := 1))
    (a d : Node Unit 1)
    (hd : freeSucc (H a)
      ([rootNode (Label := Unit) (arity := 1)].map H)
      () = some d) :
    0 ∈ lastParamLevelsNode d := by
  obtain ⟨t, ht, rfl⟩ := freeSucc_eq_some_data hd
  rw [lastParamLevelsNode_child]
  have hlevels : levelList t =
      (([rootNode (Label := Unit) (arity := 1)] :
         List (Node Unit 1)).map H).map Node.level := by
    rw [← map_level_paramNodes]
    exact congrArg (List.map Node.level) ht
  rw [hlevels]
  simp [hroot, rootNode]

/-- Transport a marked outgoing source edge into the image of
any sufficiently high node under a root-fixing shape map. -/
theorem root_marker_transported_along_successor
    (H : ShapeMap (freeSTree (Label := Unit) (arity := 1)))
    (hroot : H (rootNode (Label := Unit) (arity := 1)) =
      rootNode (Label := Unit) (arity := 1))
    {a b z : Node Unit 1}
    (hstep : freeSucc a
      [rootNode (Label := Unit) (arity := 1)] () = some b)
    (hbz : b ≤ z) :
    HasRootMarkerAt (H z) (H a).level := by
  obtain ⟨d, hd, hdb⟩ := H.weak_succ' hstep
  have hdlev : d.level = (H a).level + 1 :=
    node_covBy_level (freeSucc_s1 hd).1
  exact ⟨d, hdb.trans (H.map_le_of_le hbz), hdlev,
    image_root_successor_has_marker H hroot a d hd⟩

end SuccessorTree.FreeAncestral
