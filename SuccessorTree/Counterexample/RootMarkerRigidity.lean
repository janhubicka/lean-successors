import SuccessorTree.Counterexample.MaskCodes
import Mathlib.Tactic

/-!
# Retained successor levels cannot carry the original-root marker

This is the core **universal** half of the marker obstruction in the
Theorem 1.11 counterexample. It applies to *any* shape map of the
free ancestral successor tree whose image of the root has positive level.

Every retained image level has a mandatory outgoing successor edge.
All its parameters are images of source nodes, hence lie strictly above
the original root. It therefore cannot carry the root-marker code.

The complementary fact--skipped levels of the specific Q_A maps have
root markers, preserved by pure outer maps--is proved separately.
-/

namespace SuccessorTree.FreeAncestral

/-- The outgoing edge immediately after target level m has the original
root as one of its ancestral parameters. -/
def HasRootMarkerAt (x : Node Unit 1) (m : Nat) : Prop :=
  ∃ y : Node Unit 1,
    y ≤ x ∧ y.level = m + 1 ∧
      0 ∈ lastParamLevelsNode y

/-- Positive image of the original root forces every image node to
lie on a positive level. -/
theorem shapeMap_image_level_pos
    (G : ShapeMap (freeSTree (Label := Unit) (arity := 1)))
    (hroot : 0 < (G (rootNode (Label := Unit) (arity := 1))).level)
    (x : Node Unit 1) : 0 < (G x).level := by
  have hle : G (rootNode (Label := Unit) (arity := 1)) ≤ G x :=
    G.map_le_of_le (root_le x)
  exact lt_of_lt_of_le hroot (node_level_le hle)

/-- Any free successor with parameters from the range of G
has no original-root parameter when G sends the root above level 0. -/
theorem mapped_successor_avoids_root
    (G : ShapeMap (freeSTree (Label := Unit) (arity := 1)))
    (hroot : 0 < (G (rootNode (Label := Unit) (arity := 1))).level)
    (a : Node Unit 1) (p : List (Node Unit 1)) (c : Unit)
    (d : Node Unit 1)
    (hd : freeSucc (G a) (p.map G) c = some d) :
    0 ∉ lastParamLevelsNode d := by
  obtain ⟨t, htp, rfl⟩ := freeSucc_eq_some_data hd
  rw [lastParamLevelsNode_child]
  have hlevel : levelList t = (p.map G).map Node.level := by
    rw [← map_level_paramNodes]
    rw [htp]
  rw [hlevel]
  intro hz
  obtain ⟨y, hy, hyzero⟩ := List.mem_map.mp hz
  obtain ⟨x, hx, hxy⟩ := List.mem_map.mp hy
  have hpos := shapeMap_image_level_pos G hroot x
  rw [← hxy] at hpos
  omega

/-- In the rooted free history tree, prefixes on equal levels of
the same total history are literally equal. -/
theorem equal_prefix_of_equal_level
    {x y z : Node Unit 1}
    (hx : x ≤ z) (hy : y ≤ z)
    (hlevel : x.level = y.level) : x = y := by
  rcases node_lower_linear hx hy with hxy | hyx
  · exact node_eq_of_le_level_eq hxy hlevel
  · exact (node_eq_of_le_level_eq hyx hlevel.symm).symm

/-- If b is an actual source successor of a, every sufficiently high
G-image node lies above the mandatory outgoing successor at level G(a).
That target edge cannot have the original-root marker. -/
theorem retained_level_avoids_root
    (G : ShapeMap (freeSTree (Label := Unit) (arity := 1)))
    (hroot : 0 < (G (rootNode (Label := Unit) (arity := 1))).level)
    {a b z : Node Unit 1} {p : List (Node Unit 1)} {c : Unit}
    (hsucc : freeSucc a p c = some b)
    (hbz : b ≤ z) :
    ¬ HasRootMarkerAt (G z) (G a).level := by
  rintro ⟨v, hvz, hvlev, hvroot⟩
  obtain ⟨d, hd, hdb⟩ := G.weak_succ' hsucc
  have hdlev : d.level = (G a).level + 1 :=
    node_covBy_level (freeSucc_s1 hd).1
  have hdz : d ≤ G z := hdb.trans (G.map_le_of_le hbz)
  have hvd : v = d :=
    equal_prefix_of_equal_level hvz hdz (hvlev.trans hdlev.symm)
  subst v
  exact mapped_successor_avoids_root G hroot a p c d hd hvroot

end SuccessorTree.FreeAncestral
