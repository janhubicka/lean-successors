import SuccessorTree.V10.ContainedCanonicalParameter
import SuccessorTree.V10.ShapeMapParameterPrefix
import Mathlib.Tactic

/-!
# Complete image ordinary type in ONE containing node

For a genuine partial structure A and a type vertex v of large free
cut, let j be an ordinary vertex whose own free cut contains n>0.
The source type of j through n is an actual canonical parameter
prefix of the step which adds j inside the type of v.

After an arbitrary ShapeMap F, the full L+ type of its image ordinary
coordinate inside F(type(v)) is precisely F(type^n(j)).
No extra age preservation, M2, or finite-amalgamation assumption.
-/

namespace SuccessorTree.V10

/-- Every retained positive-source parameter prefix occurs as its
complete mapped ordinary-vertex type in the SAME image node. We
retain the actual source coordinate a in the conclusion, so the
coordinate can subsequently be identified with the level map
of F, rather than inventing or assuming any numerical coordinate. -/
theorem shapeMap_transports_ambient_ordinary_type
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : EnumeratedPartialStructure db du dd)
    (v j n : Nat) (hv : v < A.size)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hCut : j + 1 ≤ A.freeLevel v)
    (hPos : 0 < A.freeLevel j)
    (hn : n ≤ A.freeLevel j)
    (u t : AdmissibleKptNode family)
    (hu : u.1 = A.rawTypeAtFree v)
    (ht : t.1 =
      (⟨n, A.partialTypeAt n j⟩ : RawPartialTypeNode db du dd)) :
    ∃ (a : AdmissibleKptNode family)
      (hAddress : LevelTree.lev (F a) < LevelTree.lev (F u))
      (hSocle : LevelTree.lev (F t) ≤ LevelTree.lev (F u)),
      LevelTree.lev a = j ∧
      (F u).1.2.ordinaryType
        (LevelTree.lev (F a)) hAddress
        (LevelTree.lev (F t)) hSocle = (F t).1.2 := by
  obtain ⟨a,b,p,c,q,hSucc,hBelow,hMem,hQ,hLevA⟩ :=
    ambient_prefix_actual_parameter_below
      family A v j hv hAvoid hCut hPos
  let u0 : AdmissibleKptNode family :=
    ⟨A.rawTypeAtFree v, ⟨A,v,hv,hAvoid,rfl⟩⟩
  have hu0 : u = u0 := Subtype.ext hu
  have hBelow' : b ≤ u := by
    rw [hu0]
    exact hBelow
  have hLevQ : LevelTree.lev q = A.freeLevel j := by
    have h := congrArg Sigma.fst hQ
    exact h
  have hLevT : LevelTree.lev t = n := by
    have h := congrArg Sigma.fst ht
    exact h
  have hnQ : n ≤ LevelTree.lev q := by
    rw [hLevQ]
    exact hn
  have htq : t ≤ q := by
    change t.1 ≤ q.1
    rw [ht,hQ]
    refine ⟨hn,?_⟩
    exact (A.partialTypeAt_restrict n (A.freeLevel j) j hn).symm
  have hAncestor : LevelTree.ancestor q n hnQ = t :=
    (LevelTree.eq_ancestor_of_le htq hLevT hnQ).symm
  obtain ⟨hAddress,hSocle,hType⟩ :=
    shapeMap_transports_parameter_prefix
      family F hSucc hBelow' q hMem n hnQ
  rw [hAncestor] at hSocle hType
  refine ⟨a,hAddress,hSocle,hLevA,?_⟩
  exact hType

end SuccessorTree.V10
