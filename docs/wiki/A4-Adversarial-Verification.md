# Adversarial audit of fat-tree A4

The fat-tree A4 proof is one of the reusable core results of
`lean-successors`. It is checked at the exact `SMTree` interface,
with no assumption of a prior A4 or Ellentuck theorem.

Three *automated* independent regression reviews run on the pinned
Lean source, rather than trusting the output of a single proof file.
These are independent test routes, **not separate human referees**.

## Referee A — unconditional theorem endpoints

`scripts/RefereeFatTreeA4A.lean` imports the public
`FatTree.A4ReviewComplete` module and reconstructs the required
theorem types using only the stated `SMTree` hypotheses. Its four
transitive `#print axioms` checks include the fixed-stem pigeonhole,
A4, abstract Ramsey space and Ellentuck endpoints. Every report must
use only the permitted standard Lean axioms.

## Referee B — awkward boundary configurations

`scripts/RefereeFatTreeA4B.lean` checks genuine one-level source
letters, root cuts with no available source letter, moving roots,
trace extension and last-block coverage. It separately audits six
named axioms reports. These tests are deliberately not replaced by
the generic finite-dimensional Ramsey theorem.

## Referee C — dependency firewall

`scripts/check-fat-tree-a4-firewall.py` traverses all reachable
project imports below `FatTree.A4ReviewSourceFusion`, rejects
admission tokens, and rejects importing the A4 assembly or a
prior Ellentuck theorem. This is a syntactic safety test: it does
**not** replace the Lean kernel or detect arbitrary mathematical
errors in a correct but mismatched statement.

## Running the audit

The [Adversarial fat-tree A4 workflow](https://github.com/janhubicka/lean-successors/actions/workflows/adversarial-fat-tree-a4.yml)
runs weekly from the default branch and can be dispatched manually.
Updates to the workflow or the firewall script trigger a PR validation.

The current workflow uses one shared pinned Lake workspace, builds
`SuccessorTree.FatTree.A4ReviewComplete`, runs all three independent
checks, and retains exact-head logs and the commit SHA. The complete
project's normal Lean CI separately tests the same main theorem and
its proof-route independence.

To reproduce the checks locally:

```bash
lake build SuccessorTree.FatTree.A4ReviewComplete
lake env lean scripts/RefereeFatTreeA4A.lean > referee-a.log
python3 scripts/check-axiom-log.py referee-a.log 4
lake env lean scripts/RefereeFatTreeA4B.lean > referee-b.log
python3 scripts/check-axiom-log.py referee-b.log 6
python3 scripts/check-fat-tree-a4-firewall.py
```

An implementation cleanup can break internal declaration and file
APIs; no compatibility wrappers are required. A change to the
mathematical theorem, the valid proof dependencies or M1–M3 is a
separate reviewed mathematical change, not something this workflow
should silently accommodate.
