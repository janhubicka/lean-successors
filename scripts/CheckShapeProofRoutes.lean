import SuccessorTree.ShapeFiniteRamsey
import SuccessorTree.ShapeEllentuckRamsey
import SuccessorTree.ShapeFiniteCorollaries
import Lean

/-!
Regression checks for the two proofs of the finite-dimensional shape theorem.
An import check is insufficient: the shared structural files also expose the
direct theorem. Inspect project constants in the elaborated proof terms instead.
The separate axiom reports below cover dependencies outside this project too.
-/

open SuccessorTree SuccessorTree.SMTree

section Statements
universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

example (H : SMTree S) (n k r : Nat) (colour : AM H n k → Fin r) :
    ∃ W : ShapeSubspace H n, ∀ a b : AM H n k,
      colour (H.shapeActK n k W a) = colour (H.shapeActK n k W b) :=
  H.shapePreservingRamsey_viaFatEllentuck n k colour

example (H : SMTree S) (colour : AM H 0 0 → Fin 2) :
    ∃ W : ShapeSubspace H 0, ∀ a b : AM H 0 0,
      colour (H.shapeActK 0 0 W a) = colour (H.shapeActK 0 0 W b) :=
  H.shapePreservingRamsey_viaFatEllentuck 0 0 colour

example (H : SMTree S) (n k m r : Nat) (hk : 0 < k) (hm : 0 < m) :
    ∃ N : Nat, ∀ colour : AM.AtMost H n k N → Fin (r + 1),
      ∃ f : AM.AtMost H n m N, ∀ g h : AM.Below H n k (n + m),
        colour (boundedComp H hm hk f g) = colour (boundedComp H hm hk f h) :=
  H.shapeRamsey_bounded n k m hk hm

example (H : SMTree S) (n k m r : Nat) (hk : 0 < k) (hm : 0 < m) :
    ∃ N : Nat, ∀ colour : AM.At H n k N → Fin (r + 1),
      ∃ f : AM.At H n m N, ∀ g h : AM.At H n k (n + m - 1),
        colour (exactComp H hm hk f g) = colour (exactComp H hm hk f h) :=
  H.shapeRamsey_exact n k m hk hm

end Statements

open Lean

private def isProjectConstant (name : Name) : Bool :=
  "SuccessorTree.".isPrefixOf name.toString ||
    "_private.SuccessorTree.".isPrefixOf name.toString

private partial def projectDependencies
    (env : Environment) (pending : List Name) (seen : NameSet := {}) :
    Except String NameSet := do
  match pending with
  | [] => return seen
  | name :: rest =>
      if seen.contains name || !isProjectConstant name then
        return ← projectDependencies env rest seen
      let some info := env.checked.get.find? name
        | throw s!"Missing project declaration: {name}"
      let typeNames := info.type.getUsedConstants.toList
      let names := match info with
        | .defnInfo v => typeNames ++ v.value.getUsedConstants.toList
        | .thmInfo v => typeNames ++ v.value.getUsedConstants.toList
        | .opaqueInfo v => typeNames ++ v.value.getUsedConstants.toList
        | .inductInfo v => typeNames ++ v.ctors
        | _ => typeNames
      projectDependencies env (names ++ rest) (seen.insert name)

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let direct := ``SuccessorTree.SMTree.shapePreservingRamsey
  let viaFat := ``SuccessorTree.SMTree.shapePreservingRamsey_viaFatEllentuck
  let directOne := ``SuccessorTree.SMTree.shapeOneDimensionalRamsey
  let fatEllentuck := ``SuccessorTree.SMTree.FatTree.fatTreeEllentuck
  let common := ``SuccessorTree.SMTree.shapePreservingRamsey_of_oneDimensional
  for (root, required, forbidden) in
      [(direct, [directOne, common], [fatEllentuck, viaFat]),
       (viaFat, [fatEllentuck, common],
         [direct, directOne,
          ``SuccessorTree.SMTree.shapeRamsey_approximations,
          ``SuccessorTree.SMTree.shapeLocalPigeonhole,
          ``SuccessorTree.SMTree.buildShapeProductStep])] do
    let deps ← match projectDependencies env [root] with
      | .ok deps => pure deps
      | .error message => throwError m!"{message}"
    for name in required do
      unless deps.contains name do
        throwError m!"{root} does not use the required proof input {name}"
    for name in forbidden do
      if deps.contains name then
        throwError m!"{root} unexpectedly depends on {name}"
    logInfo m!"PASS: {root} uses its own Ramsey input and the shared induction"

#print axioms SuccessorTree.SMTree.shapeRamsey_one_relative_of_oneDimensional
#print axioms SuccessorTree.SMTree.shapeRamsey_approximations_of_oneDimensional
#print axioms SuccessorTree.SMTree.shapePreservingRamsey_of_oneDimensional
#print axioms SuccessorTree.SMTree.shapePreservingRamsey
#print axioms SuccessorTree.SMTree.FatTree.shapeOneDimensionalRamsey_viaFatEllentuck
#print axioms SuccessorTree.SMTree.shapePreservingRamsey_viaFatEllentuck
#print axioms SuccessorTree.SMTree.shapeRamsey_bounded
#print axioms SuccessorTree.SMTree.shapeRamsey_exact
#print axioms SuccessorTree.SMTree.FatTree.tailMap_zero_eq_associatedMap
#print axioms SuccessorTree.SMTree.FatTree.tailMap_ofShapeMap
