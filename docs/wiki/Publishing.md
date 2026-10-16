# Publishing the source-controlled successor wiki

The reviewed source of truth is `docs/wiki/` in the repository.
The `publish-wiki.yml` GitHub Action follows the pattern used in
`janhubicka/lean-milliken`: it synchronizes documentation from the
main branch to GitHub's independent `.wiki.git` repository.

GitHub's wiki repository must first be initialized by creating one
`Home` page on the [Wiki tab](https://github.com/janhubicka/lean-successors/wiki).
Until then the workflow deliberately emits a notice and succeeds
without pretending the wiki was published. Once initialized, edits to
`docs/wiki/**` on main or a manual workflow dispatch publish all
pages, including `_Sidebar.md`.

Only merge documentation whose theorem status agrees with exact-head
Lean/axiom evidence. When editing a mathematical claim, update
`Theorems-and-Manuscript.md` and the adversarial ledger as needed.
Historical partial/open checkpoints remain part of the audit trail
but must not be mistaken for the latest result.

External files outside `docs/wiki/` should be linked by repository
URLs when wiki-relative paths would not resolve after publication.
