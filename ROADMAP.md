# Formalization roadmap

## Paper-to-Lean map

| Paper ingredient | Lean target | Status |
|---|---|---|
| starred line `L`, evaluations `L(c)`, `L(*)` | `StarLine` | proved |
| fixed word `s` containing every `Γ`-letter | `fullSupport`, `Supports` | proved |
| HJ after the support prefix | `supportedStarHJ` | proved from `StarHJ` |
| recursive history `g_w` | `ReplaySystem.wordApprox` | interface |
| M3 replay construction of `h` | `ReplaySystem.replay` | interface; structural phase |
| `h ∘ Id = g_{L(*)}` | `replay_base` | interface; next target |
| `h ∘ e = g_{L(e)}` | `replay_letter` | interface; next target |
| 1-dimensional pigeonhole | `oneDimensionalPigeonhole` | proved from the two inputs above |
| starred Hales–Jewett theorem | `StarHJ` | proof source audited; Lean formalization next |

## Structural order

The next files should be added in this dependency order:

1. `SuccessorTree/HalesJewett/VariableWord.lean`: substitution and `Shift`.
2. `SuccessorTree/HalesJewett/Large.lean`: large sets and the forcing lemmas.
3. `SuccessorTree/HalesJewett/AlphabetInduction.lean`: increase alphabet size and discharge `StarHJ`.
4. `SuccessorTree/Tree.lean`: rooted levelled trees and restriction to levels.
5. `SuccessorTree/Successor.lean`: successor operation, parameters and character.
6. `SuccessorTree/ShapePreserving.lean`: definition and basic preservation lemmas.
7. `SuccessorTree/Approximation.lean`: finite approximations and level maps.
8. `SuccessorTree/Monoid.lean`: M1–M3.
9. `SuccessorTree/Canonical.lean`: canonical extension.
10. `SuccessorTree/Replay.lean`: actual M3 replay block; instantiate `ReplaySystem`.
11. derive a bounded finite starred HJ form by compactness when the finite successor theorem needs an explicit bound.

The point of the interface boundary is auditability: if the tree-specific
formalization accidentally assumes more than M1–M3, it will become visible
when instantiating `ReplaySystem`.
