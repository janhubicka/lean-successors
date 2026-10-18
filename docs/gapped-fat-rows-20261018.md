# Gapped fat rows: minimal structural change (18 October 2026)

The author clarified that **the same existing fat-tree cuts** should be movable inside gaps between consecutive visible tree levels, and that **a line is one complete one-variable block**. Do NOT add a second independent cutting-mark sequence as an unrelated fat-tree field. The schedule in `Block/MarkedCuts.lean` is a derived index view.

## Correct row data

Original strong fat trees use a width-one approximation `a_i ∈ AM^(c_i)_1`, ending at image level `m_i`, with the next cut forced to `c_(i+1)=m_i+1`.

Replace the row in the *experimental gapped space* with a width-two approximation

    u_i ∈ AM^(c_i)_2,
    levelMap(u_i, c_i + 1) = c_(i+1).

The visible (internal branching) level is derived, not stored separately:

    ell_i = levelMap(u_i, c_i).

Strictly increasing image levels imply

    c_i <= ell_i < c_(i+1) <= ell_(i+1).

This uses exactly one cut sequence `c`. The row is a single extendible full-frontier witness, not a pair of separately extendible initial/final pieces. Under weak M2, its canonical extension exists. This is a *representation/model*, not yet the new weak A4 theorem.

For words, a line `b(v)=h v t(v)` with constants h before first variable has a row on a source cut c:

    u(z)=z h                      (|z|=c)
    u(z a)=z h a t(a)            (|za|=c+1).

It fixes levels below c, branches at ell=c+|h|, and ends at c+|b|. For `00v1v0`, the branch is two positions after left cut and the right cut is only after all occurrences. The classic bad block `v0v` is permitted; never require separate globally admissible factors on either side of its first variable.

## Original fat rows embed

Given old row `a_i ∈ AM^(c_i)_1(m_i)` with c_(i+1)=m_i+1, put

    u_i = (a_i)^+ restricted to T(<c_i+2).

This has internal level m_i, right cut m_i+1, and uses unchanged c. Thus the old space is a special case of the new row geometry at the object level. This does NOT automatically identify the old and new reduction relations.

## Lean checkpoint

`SuccessorTree/FatTree/GappedBasic.lean` now introduces `GappedFatTree H` with one `cut` field, width-two `AM` rows, and derived `visible`; proofs give interleaving and produce `Block.MarkedLevelSchedule`. For testing the existing finite approximation infrastructure, the file is parameterised by the current *strong* Lean record `SMTree`, so this is not yet the new weak-tree record or a Ramsey proof. The strong record, old FatTree implementation, envelope code and main branch are untouched.

## Distinguish three word constructions

* Full adjacent marked fat-tree lines: **current project**. Rebuild the lift at the right cut using the *whole* width-two row; old `Lift` would append one successor too many.
* Carlson-style extracted words by selecting nonadjacent ambient lines: **later separate project**. The extracted theorem might be proved by a thinning schedule, but transfer back to full fat trees needs a padding/completion relation, full-frontier proof and colour control for omitted lines. No such theorem is asserted here.
* Unmarked shape-map reduction: independent algebraic right-composition; inserting marks does not automatically transfer Ramsey results to it.

## Immediate next proof

Define one-step gapped lift from level c_i to c_(i+1) using `u_i` on source levels c_i and c_i+1, **without** inserting an additional successor after `u_i^+`. Define an exact-trace marked reduction that respects full-frontier blocks and marks. Prove its A1--A3 before any A4 claim. Only then re-test the parity obstruction in that exact space. Keep the parity counterexamples to the prior prototype conventions separate.

The companion source patch `successor-v20-gap-fat-width-two.patch` modifies the gapped-cut appendix of the last marked-word proof source; it leaves M1--M4, strong M2'/M3', applications and envelopes unchanged.
