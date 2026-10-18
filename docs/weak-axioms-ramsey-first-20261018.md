# Weak axioms: Ramsey-first branch checkpoint

Date: 18 October 2026.

Branch: `weak-axioms-ramsey-first-20261018`; draft PR #578, based on the checked EA branch #577. Do not merge the experimental axiomatization into main. Work on the Ramsey statements before broad record/interface plumbing.

## Terminology and scope

An unqualified **(S,M)-tree** means the new compact M1–M4 package, with its designated alphabets. A **strong (S,M)-tree** additionally has the original decomposition/duplication conditions M2′–M3′ (which imply the weak package). M1 is the unchanged closed-monoid axiom.

The goal is shape-preserving and block-fat Ramsey theory without the primed hypotheses. This is a target, not an already validated consequence: the manuscript's genuine parity monoid satisfies the present local package and refutes the unrestricted original map Ramsey conclusion. We must resolve relative coverage/persistence or specify the appropriate generated front; we cannot delete a strong hypothesis by renaming it.

Keep envelopes, the minimal-envelope algorithm, and existing big-Ramsey applications under the strong assumptions. Later experiments with weak envelopes are separate. Legacy Lean `SMTree` remains the strong record until the mathematical Ramsey route is settled; the new core does not import it.

## Kernel-checked first theorem layer

File: `SuccessorTree/Block/SeededPigeonhole.lean`.

`HasSeededRealisation wordApprox apply` states exactly

    exists seed, forall starred line L, exists one block b,
      apply b base = wordApprox (seed ++ L.star), and
      forall e, apply b (letter e) = wordApprox (seed ++ L.eval e).

The seed precedes the line and colouring. The witness is simultaneous in every letter, and the starred input is not identity substitution into the variable positions.

Checked endpoints:

1. `seededPigeonhole`: local homogeneity with starred Hales–Jewett discharged.
2. `seededPigeonhole_pairwise`: pairwise line formulation.
3. `finiteProfilePigeonhole`: one block works for a finite family of profile colourings.
4. `coveredFrontPigeonhole`: conditional coverage/common-base transfer.
5. `hasSeededRealisation_of_replay`: old supported replay implies the seeded interface; no unseeded claim.
6. `singletonRealisation`: a nonempty alphabet can see only one point.
7. `fullFront_not_homogeneous`: that represented point cannot be enlarged to an arbitrary Boolean front.

The final two items are finite abstract-interface counterexamples, NOT claimed to be successor monoids. The separate manuscript parity construction is the genuine monoid obstruction.

## Exact proof evidence

Proof commit: `70ae3b4e71de18d16dae2276a389574fc05da7d9`.

Focused run: https://github.com/janhubicka/lean-successors/actions/runs/39128732027

The workflow explicitly checked out that commit, built the new module (3,157 build jobs including dependencies), and emitted all seven named axiom reports. The first five use only `propext`, `Classical.choice`, and `Quot.sound`; the last two use no axioms. The exact-name checker reported `PASS: 7 reports use only standard Lean axioms`. The source-integrity gate scanned 604 Lean source files with no admission or source-axiom declaration.

Artifact `weak-axioms-ramsey-core`, ID `12137217563`, reported ZIP SHA-256 `18b064bdf4ad2d072dcacf1432a36d3bac2577d59f7159045108eedc797dfd0a`. The artifact contains the exact COMMIT, build log, axiom reports, toolchain, Lake configuration/manifest, and checksums. The report is read from the actual workflow log; no claim is made here to have downloaded and independently verified the ZIP bytes.

The certificate is for the generic Ramsey core under its explicit colour-free input. A complete typed weak tree record and the constructor interpreting manuscript finite functions are deliberately deferred. This does not certify full M1–M4, weak fat A4, or weak infinite-dimensional Ramsey theory.

## English proof and adversarial audit

Fix the seed s. Apply the already checked starred Hales–Jewett theorem to the colouring w -> colour(wordApprox(s ++ w)). Realise its line by one block. The realisation equations transfer all colours, including the starred colour. No decomposition, fusion, canonical completion beyond what is used to define wordApprox, or strong-tree field appears in this proof.

For finitely many maps tau_i, use the tuple colouring t -> (colour(tau_i(t)))_i. Equality of tuples gives one block which is homogeneous separately in every profile. This is stronger than separate existential witnesses but does not say that different profiles share one colour. A common base makes their colours agree. Without a common base, coverage only gives a bound of at most the number of profiles.

Coverage is an inclusion for every member of the family, not a list of selected representatives. A fixed finite set of profiles and a finite alphabet represent only finitely many points. Thus the covered-front theorem is a **bounded-stage** tool. It cannot directly represent the entire unbounded A4 front by a fixed finite family. Nonemptiness is also separate; an empty covered family yields no useful A4 refinement.

The code's conditional bridge is NOT a new axiom. Its coverage/common-base conditions are sufficient local data, not claimed necessary or minimal. No source condition has been strengthened merely to make the proof compile.

## Next mathematical checkpoint

IMPORTANT UPDATE: the parity monoid also refutes the ORIGINAL fat-tree A4 and the BRANCH-FIRST completed-block fat-tree A4 under weak M1–M4. Thus the following staged-fusion scheme is a research target only AFTER strengthening the colour-free hypotheses or restricting the Ramsey conclusion; it cannot prove the unrestricted theorem from the current package.

For each completed stem and ambient block tree, organise admissible one-block extensions into finite batches ending at actual ambient line boundaries. Prove a relative simultaneous realisation for each batch, represent every extension in that batch, and retain the completed stem. Show that the decisions persist under later aligned reductions. Only then run one fusion and prove that every extension in its limit appeared in a controlled batch. Resolve any different base colours rather than treating coordinatewise tuple homogeneity as global homogeneity.

Do not:

- cut inside an unfinished output block;
- move a committed endpoint when inserting a recording word;
- use unrelated witnesses at successive stages;
- infer global admissible right factorisation from geometric containment;
- assume the literal all-trace Ramsey theorem in a field named coverage or realisation;
- broaden the designated alphabet without verifying its realisation condition;
- reuse the old fat-tree theorem for the changed row convention by renaming its objects.

The next proof should provide this finite-stage/persistence step. Broad API renaming, manuscript-to-LevelTree plumbing, concrete EA witnesses and envelope simplification are not the next task.

## Manuscript checkpoint

The companion patch is against `successor-v20-compact-axioms-sources.tgz`, SHA-256 `83faf741dec0ff77b25fd1dbd4125bb2af238573e5c8ba96c438a72855aa207a`. It removes the convention that an unqualified (S,M)-tree secretly means strong, labels every changed strong use explicitly, and adds the finite-profile proof and bounded-front caveat. M1 and the primed-axiom definition are byte-for-byte unchanged. Appendix A and the application implementations are unchanged. The envelope text only gains explicit strong scope; the algorithm is not modified.

The marker on the manuscript local lemma is an **interface** marker: it points to the checked generic proof, not a completed source-to-Lean constructor. No new global Ramsey theorem is marked green.


## 18 October: two rigorous fat A4 counterexamples

The genuine weak ordered-word monoid M_odd from manuscript Appendix B has arbitrary initial constant heads; every completed variable block starts with x, contains an odd number of occurrences of x and an even number of constant 1's. The earlier manuscript checked M1–M4 with singleton designated neutral alphabets.

1. **Original fat convention:** For any ambient fat tree U, let its first head be c and its second row complete the prior variable with w(x). The two-row root lift is {c w(a) b : a,b in {0,1}}. For each a, a new first row with head c w(a), followed by the ambient rows beginning with row 2, gives a legal reduction. The cut map is 0→0 and i≥1→i+1; first full-lift inclusion and all later equalities hold. Since w has odd variable multiplicity, the two heads have opposite parity. Thus the first-row head-parity colouring violates A4 at the empty stem; its cylinder is Ellentuck-clopen and not Ramsey.

2. **Branch-first completed-block convention:** In any ambient tree take blocks w0,w1,w2,w3, with odd variable counts m0,m1,m2,m3. Two of m1,m2,m3 have the same residue (1 or 3) mod 4; say j<k. Form v(x)=w0(x)t1(x)...tk(x), where tj=wj(x), tk=wk(x), and all other ti=wi(0). This begins with x, has odd variable count m0+mj+mk ≡ m0+2 mod 4, and even constant-1 parity. Therefore v is a legal parity block. Both its evaluations occur in the ambient first k+1-block span, with choices a at positions 0,j,k and 0 elsewhere. Grouping these rows into the new first row and retaining the rest gives an actual aligned block-fat reduction. Hence first-row variable-count mod 4 is persistently bichromatic below every ambient block-fat tree. A4 and clopen Ramsey fail for this convention too.

The mod-four argument needs no arbitrary internal-cut extraction, and the reductions preserve complete ambient line boundaries. These are not merely gaps in the proposed good-pair proof: they disprove the intended unrestricted conclusion from weak M1–M4.

### Formal and diagnostic evidence

Exact proof commit: `7abbbe44e4eb131d166e3b543876e0c4f53bc2eb`. Focused GitHub Actions run: https://github.com/janhubicka/lean-successors/actions/runs/39137602165 — **success, 18 exact named axiom reports**, 606-file integrity check. The kernels are:
- `ParityFat.two_first_rows_opposite`: two candidate one-row full lifts contained in the old two-row lift, with opposite head parity.
- `ParityFat.four_blocks_flip`: admissible grouped block, literal two-input span containment, and variable-count mod-four flip.
- `ParityFat.firstRowHomogeneity_false_of_splitting`: purely logical A4 obstruction under the explicitly stated splitting hypothesis.

The infinite parity-monoid interpretation and full reduction-tail splice are proved in English, **not** by these Lean declarations. The corresponding manuscript markers must therefore be interface markers.

Finite independent diagnostics: 495 head/block cases, 11,250 old-fat tail-lift checks, and 625 four-block branch-first ambient configurations. Both complete LaTeX proofs are supplied in the companion incremental manuscript patch (file `weak-fat-A4-counterexample.tex` in the patch); the full English proof and its validation boundary are also documented above in this branch note.

### Next objective

Keep the original strong Ramsey theorems and the envelope/big Ramsey section unchanged. The next mathematical priority is **finding a minimal colour-free strengthening of M4 (or a precise generated-front conclusion) that excludes both parity colourings while retaining ordered variable words**. In particular, simple coverage/persistence technical lemmas cannot do so on their own. Avoid replacing the required condition by A4 itself or by a Ramsey axiom in disguise. Resume the all-trace finite-stage proof only after identifying a viable theorem statement.
