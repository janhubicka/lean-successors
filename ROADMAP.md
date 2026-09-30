# Formalization roadmap

## Paper-to-Lean map

| Paper ingredient | Lean target | Status |
|---|---|---|
| starred line `L`, evaluations `L(c)`, `L(*)` | `StarLine` | proved |
| fixed word `s` containing every `Γ`-letter | `fullSupport`, `Supports` | proved |
| HJ after the support prefix | `supportedStarHJ` | proved from `StarHJ` |
| recursive history `g_w` | `ReplaySystem.wordApprox` | interface |
| M3 replay construction of `h` | `ReplaySystem.replay` | interface; next target |
| `h ∘ Id = g_{L(*)}` | `replay_base` | interface; next target |
| `h ∘ e = g_{L(e)}` | `replay_letter` | interface; next target |
| 1-dimensional pigeonhole | `oneDimensionalPigeonhole` | proved from the two inputs above |
| starred Hales–Jewett theorem | `StarHJ` | explicit unproved combinatorial input |

## Immediate Hales--Jewett order

Before the structural tree layer, add:

1. `SuccessorTree/VariableWord.lean`: finite/omega variable words and substitution.
2. `SuccessorTree/Shift.lean`: prefix/tail identities and substitution associativity.
3. `SuccessorTree/Large.lean`: large sets and the two forcing lemmas.
4. `SuccessorTree/Fusion.lean`: stabilization and the omega-dimensional theorem.
5. `SuccessorTree/HalesJewett.lean`: alphabet-size induction, proving `StarHJ`.

## Structural order

After `StarHJ` is discharged, add:

1. `SuccessorTree/Tree.lean`: rooted levelled trees and restriction to levels.
2. `SuccessorTree/Successor.lean`: successor operation, parameters and character.
3. `SuccessorTree/ShapePreserving.lean`: definition and basic preservation lemmas.
4. `SuccessorTree/Approximation.lean`: finite approximations and level maps.
5. `SuccessorTree/Monoid.lean`: M1–M3.
6. `SuccessorTree/Canonical.lean`: canonical extension.
7. `SuccessorTree/Replay.lean`: actual M3 replay block; instantiate `ReplaySystem`.
8. `SuccessorTree/HalesJewett.lean`: finite starred HJ.

The point of the interface boundary is auditability: if the tree-specific
formalization accidentally assumes more than M1–M3, it will become visible
when instantiating `ReplaySystem`.
