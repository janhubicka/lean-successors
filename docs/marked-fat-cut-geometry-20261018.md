# Cutting marks separate from visible fat-tree levels (18 October 2026)

**Status:** correction to the experimental weak-axiom fat-tree model. Keep the branch draft and do not infer weak A4 from the old theorem or from the numerical index calculus.

## Geometry

Use two strictly increasing sequences: visible levels `ell_i`, cutting coordinates `c_i`, with `c_0=0` and

    c_i <= ell_i < c_(i+1) <= ell_(i+1).

A cut coordinate c denotes the **gap immediately before** level c, so a cut exists between adjacent integer levels. The line/block indexed i starts at mark c_i, contains its distinguished level ell_i internally, and ends at c_(i+1). Marks and visible levels are independent in the weak construction.

In an ordered word, if x_i first appears at position a_i and last appears at b_i, then `a_i<=b_i<a_(i+1)`; any choice `b_i<c_(i+1)<=a_(i+1)` is possible. For a word beginning `x0 0 x0 0 0 x1`, cut c_1 may equal 3, 4 or 5. The **underlying unmarked prefix map** still cuts immediately *before first occurrences* of the next variables (at the a_i); the optional marks only change how the marked lines allocate constants. Truncating that map at the optional marks would produce a different map and is not claimed.

A marked reduction requires two increasing index maps `phi` and `psi`, with `psi(0)=0`, matching respectively the visible levels and marks, and with

    psi(i) <= phi(i) < psi(i+1).

Both index maps compose independently, and the interlacing survives. This is **necessary, not sufficient** for a fat reduction: one also needs admissible whole-frontier successor profiles and full-lift inclusion. A line can contain skipped ambient visible levels even though it has just one distinguished *new* level. We cannot outlaw repetition across those skipped levels by bookkeeping alone.

## Referee warnings

1. A numerical gap may lie before the active variable's **last** occurrence. That does not close a block; require a cuttable profile witness, not just inequalities.
2. Do not demand separate global monoid factorizations for the neutral segment and live-variable segment. `x0x` obstructs exactly this old M2' formulation. The complete marked line must have a *single coherent, extendible* whole-frontier certificate.
3. A fixed unmarked map can have many admissible marked presentations. Fusion of unmarked maps does not stabilise chosen marks. The marked space must store marks in finite approximations and reprove closedness/A3 with them.
4. The old original-fat and endpoint-aligned branch-first parity propositions apply to those **explicit prototype spaces**. They neither prove nor disprove A4 for the corrected marked space. The four-block mod-four candidate passes the numeric interleaving check; only the as-yet-unwritten semantic reduction test will determine whether it persists. Merely adding marks is not a Ramsey proof.
5. Full duplication M3' may eventually normalize the marks, but the normalization must be proved. Weak map-to-fat widening for the old convention is not automatically a marked widening theorem.
6. The original raw shape-map Ramsey counterexample remains valid regardless of where fat marks are placed; a weak fat theorem, if available, needs a carefully qualified transfer to raw maps.

## Validation

`SuccessorTree/Block/MarkedCuts.lean` checks the interleaving, independent level/mark index embeddings, reflexivity and transitivity, and support-separated cut choices without importing the strong-tree record. Exact checkpoint `f913c7ba95ae82ca70aefc5f97437455e11ce79d`, [focused CI](https://github.com/janhubicka/lean-successors/actions/runs/39141769773): passed 22 named axiom reports (4 new cut-schedule endpoints), only standard Lean axioms. This certificate concerns the **index skeleton**, not admissible marked rows or any A4 assertion.

Companion incremental TeX patch against `successor-v20-weak-fat-A4-reviewed-sources.tgz` replaces the overbroad scope interpretation, adds a marked schedule and alignment proposition with English proof, and identifies the remaining whole-frontier obligation. It changes no axioms, established strong results, envelopes or applications. The 68-page manuscript and true latexdiff compile with the original 5 inherited overfull-box warnings.

## Next actual proof obligation

Define the complete marked line data `(left cut, distinguished level, right cut, successor-profile certificate)`; then construct the full reduction relation, prove its geometric transitivity and A1--A3 and finite-stage persistence, and **re-run the parity adversary in this exact space**. Only then attempt marked A4. Keep main unchanged and the branch draft.