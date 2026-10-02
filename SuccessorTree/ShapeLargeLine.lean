import SuccessorTree.ShapeExactFactor
import SuccessorTree.ShapeLargeFusion
import Mathlib.Tactic

/-!
# A replay line inside a large set

The exact-depth fusion supplies one future level at which a large set is
unavoidable.  At that level, finite bridge codes form a finite product colour.
The one-dimensional M3/Hales--Jewett theorem then gives a whole replay line
inside the large set.  This is the direct M-map analogue of the manuscript's
"one-dimensional pigeonhole for large sets".
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Finite code for the restriction of a reduction factor through one new
source level, with all values known to lie through target level q. -/
abbrev OneStepBridgeCode
    (H : SMTree S) (n q : Nat) :=
  InitialNode T (n + 1) → InitialNode T q

/-- Code a total M-map whose image of source level n+1 is exactly q. -/
noncomputable def oneStepBridgeCodeOf
    (H : SMTree S) (K : MMap H) (n q : Nat)
    (hK : H.levelMap K.map (n + 1) = q) :
    OneStepBridgeCode H n q :=
  fun x => ⟨K x.1, by
    calc
      LevelTree.lev (K x.1) =
          H.levelMap K.map (LevelTree.lev x.1) :=
        (H.levelMap_eq K.map (a := x.1)).symm
      _ ≤ H.levelMap K.map (n + 1) :=
        (H.levelMap_strictMono K.map).monotone x.2
      _ = q := hK⟩

/-- A bridge code is valid relative to a,A when it is represented by an
M-map K which already realizes the old prefix a through A and sends the new
source level n+1 to q. -/
def OneStepBridgeValid
    (H : SMTree S)
    {n q : Nat}
    (a : RamseyApprox H (n + 1))
    (A : MMap H)
    (c : OneStepBridgeCode H n q) : Prop :=
  ∃ K : MMap H,
    ramseyApprox H (n + 1) (MMap.comp H A K) = a ∧
    H.levelMap K.map (n + 1) = q ∧
    ∀ x : InitialNode T (n + 1), (c x).1 = K x.1

/-
The proof field in the preceding subtype value is irrelevant by proof
irrelevance.  The next bundled type retains only the finite code, not the
arbitrary tail of a total representing M-map.
-/

/-- Valid finite bridge codes. -/
abbrev OneStepBridge
    (H : SMTree S)
    {n q : Nat}
    (a : RamseyApprox H (n + 1))
    (A : MMap H) :=
  {c : OneStepBridgeCode H n q // OneStepBridgeValid H a A c}

noncomputable instance oneStepBridgeFintype
    (H : SMTree S)
    {n q : Nat}
    (a : RamseyApprox H (n + 1))
    (A : MMap H) :
    Fintype (OneStepBridge H (q := q) a A) :=
  Fintype.ofFinite _

/-- A chosen total representative of a valid bridge code. -/
noncomputable def oneStepBridgeMap
    (H : SMTree S)
    {n q : Nat}
    {a : RamseyApprox H (n + 1)}
    {A : MMap H}
    (c : OneStepBridge H (q := q) a A) : MMap H :=
  Classical.choose c.2

theorem oneStepBridge_prefix
    (H : SMTree S)
    {n q : Nat}
    {a : RamseyApprox H (n + 1)}
    {A : MMap H}
    (c : OneStepBridge H (q := q) a A) :
    ramseyApprox H (n + 1) (MMap.comp H A (H.oneStepBridgeMap c)) = a :=
  (Classical.choose_spec c.2).1

theorem oneStepBridge_topLevel
    (H : SMTree S)
    {n q : Nat}
    {a : RamseyApprox H (n + 1)}
    {A : MMap H}
    (c : OneStepBridge H (q := q) a A) :
    H.levelMap (H.oneStepBridgeMap c).map (n + 1) = q :=
  (Classical.choose_spec c.2).2.1

theorem oneStepBridge_code_eq
    (H : SMTree S)
    {n q : Nat}
    {a : RamseyApprox H (n + 1)}
    {A : MMap H}
    (c : OneStepBridge H (q := q) a A)
    (x : InitialNode T (n + 1)) :
    (c.1 x).1 = H.oneStepBridgeMap c x.1 :=
  (Classical.choose_spec c.2).2.2 x

/-- Bundle an actual bridge map into its finite-code type. -/
noncomputable def oneStepBridgeOfMap
    (H : SMTree S)
    {n q : Nat}
    {a : RamseyApprox H (n + 1)}
    {A : MMap H}
    (K : MMap H)
    (hprefix :
      ramseyApprox H (n + 1) (MMap.comp H A K) = a)
    (htop : H.levelMap K.map (n + 1) = q) :
    OneStepBridge H (q := q) a A := by
  let c := H.oneStepBridgeCodeOf K n q htop
  refine ⟨c, ?_⟩
  refine ⟨K, hprefix, htop, ?_⟩
  intro x
  rfl

/-- The chosen representative of the code of K agrees with K throughout the
coded source segment. -/
theorem oneStepBridgeOfMap_agrees
    (H : SMTree S)
    {n q : Nat}
    {a : RamseyApprox H (n + 1)}
    {A : MMap H}
    (K : MMap H)
    (hprefix :
      ramseyApprox H (n + 1) (MMap.comp H A K) = a)
    (htop : H.levelMap K.map (n + 1) = q)
    (x : T) (hx : LevelTree.lev x ≤ n + 1) :
    H.oneStepBridgeMap (H.oneStepBridgeOfMap K hprefix htop) x = K x := by
  let xx : InitialNode T (n + 1) := ⟨x, hx⟩
  have hchosen :=
    H.oneStepBridge_code_eq (H.oneStepBridgeOfMap K hprefix htop) xx
  change
    K x =
      H.oneStepBridgeMap (H.oneStepBridgeOfMap K hprefix htop) x at hchosen
  exact hchosen.symm

/-- Compose a high-level finite one-step map with a finite bridge. -/
noncomputable def bridgeApplyApprox
    (H : SMTree S)
    {n q : Nat}
    {a : RamseyApprox H (n + 1)}
    (A : MMap H)
    (g : AM H q 1)
    (c : OneStepBridge H (q := q) a A) :
    RamseyApprox H (n + 2) :=
  ramseyApprox H (n + 2)
    (MMap.comp H A
      (MMap.comp H (g.representative H) (H.oneStepBridgeMap c)))

/-- A replay block at q gives a refinement in the q-neighborhood. -/
theorem replayBlock_refinement_mem
    (H : SMTree S)
    (A : MMap H) (q : Nat)
    (R : ReplayBlock H q) :
    MMap.comp H A R.toMMap ∈
      (ramseyApproximationSystem H).levelNeighborhood q A := by
  constructor
  · refine ⟨R.toMMap, ?_⟩
    intro x
    rfl
  · cases q with
    | zero => rfl
    | succ q =>
        apply Subtype.ext
        funext x
        change A (R.toMMap x.1) = A x.1
        rw [R.fixesBelow x.1 (by omega)]

/-- The representative chosen for the base member of a replay line agrees
with the replay block through the whole coded level q. -/
theorem replayApplyAM_base_representative_agrees
    (H : SMTree S)
    (q : Nat) (R : ReplayBlock H q)
    (x : T) (hx : LevelTree.lev x ≤ q) :
    (replayApplyAM H q R LineInput.base).representative H x =
      R.toMMap x := by
  have htop :=
    AM.representative_top H
      (replayApplyAM H q R LineInput.base)
  have hval := congrArg Subtype.val htop
  change
    ((replayApplyAM H q R LineInput.base).representative H).restrictLe H q =
      R.toMMap.restrictLe H q at hval
  exact congrFun hval ⟨x, hx⟩

/-- Exact persistence plus the one-dimensional pigeonhole theorem produces a
whole transported replay line contained in O. -/
theorem exactPersistent_replayLine
    (H : SMTree S)
    {n d q : Nat}
    (a : RamseyApprox H (n + 1))
    (A : MMap H)
    (ha : (ramseyFinitization H).HasDepth (n := n + 1) a A (d + 1))
    (hq : d + 1 ≤ q)
    (O : Set (RamseyApprox H (n + 2)))
    (hpersist : OneStepExactPersistent H a A O q) :
    ∃ R : ReplayBlock H q,
      ∃ c : OneStepBridge H (q := q) a A,
        ∀ x : LineInput (OneLevelLetter H q),
          H.bridgeApplyApprox A (replayApplyAM H q R x) c ∈ O := by
  classical
  let colour :
      AM H q 1 → (OneStepBridge H (q := q) a A → Bool) :=
    fun g c => decide (H.bridgeApplyApprox A g c ∈ O)
  obtain ⟨R, hR⟩ :=
    H.oneDimensionalPigeonhole_shape q colour
  let A1 : MMap H := MMap.comp H A R.toMMap
  have hA1q :
      A1 ∈ (ramseyApproximationSystem H).levelNeighborhood q A := by
    exact H.replayBlock_refinement_mem A q R
  obtain ⟨b, hbA1, hbO, hbdepth⟩ := hpersist A1 hA1q
  rcases hbA1 with ⟨X, hXaA1, hXb⟩
  rcases hXaA1.1 with ⟨K, hK⟩
  have hA1d :
      A1 ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) A :=
    H.mem_levelNeighborhood_of_le hq hA1q
  have haA1 :
      (ramseyFinitization H).HasDepth (n := n + 1) a A1 (d + 1) :=
    ((ramseyFinitization H).hasDepth_iff_of_mem_levelNeighborhood
      hA1d).2 ha
  have hKn : H.levelMap K.map n = d :=
    H.reductionFactor_level_eq_depthPred K hK hXaA1.2 haA1
  have hKtop : H.levelMap K.map (n + 1) = q :=
    H.reductionFactor_level_eq_depthPred
      (n := n + 1) (d := q) K hK hXb hbdepth
  have hprefixA :
      ramseyApprox H (n + 1) (MMap.comp H A K) = a := by
    apply Subtype.ext
    funext y
    have hXaVal := congrArg Subtype.val hXaA1.2
    change (show MMap H from X).restrictLe H n = a.1 at hXaVal
    have hyX :
        (show MMap H from X) y.1 = a.1 y :=
      congrFun hXaVal y
    have hKlev : LevelTree.lev (K y.1) < q := by
      calc
        LevelTree.lev (K y.1) =
            H.levelMap K.map (LevelTree.lev y.1) :=
          (H.levelMap_eq K.map (a := y.1)).symm
        _ ≤ H.levelMap K.map n :=
          (H.levelMap_strictMono K.map).monotone y.2
        _ = d := hKn
        _ < q := by omega
    change A (K y.1) = a.1 y
    calc
      A (K y.1) = A (R.toMMap (K y.1)) := by
        rw [R.fixesBelow (K y.1) hKlev]
      _ = A1 (K y.1) := rfl
      _ = (show MMap H from X) y.1 := (hK y.1).symm
      _ = a.1 y := hyX
  let c : OneStepBridge H (q := q) a A :=
    H.oneStepBridgeOfMap K hprefixA hKtop
  have hbaseApprox :
      H.bridgeApplyApprox A
          (replayApplyAM H q R LineInput.base) c = b := by
    apply Subtype.ext
    funext y
    have hXbVal := congrArg Subtype.val hXb
    change (show MMap H from X).restrictLe H (n + 1) = b.1 at hXbVal
    have hyX :
        (show MMap H from X) y.1 = b.1 y :=
      congrFun hXbVal y
    have hcK :
        H.oneStepBridgeMap c y.1 = K y.1 :=
      H.oneStepBridgeOfMap_agrees K hprefixA hKtop y.1 y.2
    have hKlev : LevelTree.lev (K y.1) ≤ q := by
      calc
        LevelTree.lev (K y.1) =
            H.levelMap K.map (LevelTree.lev y.1) :=
          (H.levelMap_eq K.map (a := y.1)).symm
        _ ≤ H.levelMap K.map (n + 1) :=
          (H.levelMap_strictMono K.map).monotone y.2
        _ = q := hKtop
    change
      A
        ((replayApplyAM H q R LineInput.base).representative H
          (H.oneStepBridgeMap c y.1)) = b.1 y
    rw [hcK]
    rw [H.replayApplyAM_base_representative_agrees q R (K y.1) hKlev]
    calc
      A (R.toMMap (K y.1)) = A1 (K y.1) := rfl
      _ = (show MMap H from X) y.1 := (hK y.1).symm
      _ = b.1 y := hyX
  have hbaseColour : colour (replayApplyAM H q R LineInput.base) c = true := by
    change decide
      (H.bridgeApplyApprox A
        (replayApplyAM H q R LineInput.base) c ∈ O) = true
    rw [hbaseApprox]
    exact of_decide_eq_true (by simpa using hbO)
  refine ⟨R, c, ?_⟩
  intro x
  have hxcol := congrFun (hR x) c
  have hxtrue : colour (replayApplyAM H q R x) c = true := by
    exact hxcol.trans hbaseColour
  change decide
      (H.bridgeApplyApprox A (replayApplyAM H q R x) c ∈ O) = true at hxtrue
  exact of_decide_eq_true hxtrue

end SMTree
end SuccessorTree
