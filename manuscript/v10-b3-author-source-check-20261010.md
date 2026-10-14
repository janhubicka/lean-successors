# Application to the actual uploaded V10 manuscript (2026-10-10)

The user supplied `successor-v10(4).tgz` with a complete Overleaf Git tree
at source commit `d502596`. Its main file is `main.tex`, and the
boring-extension statement is labelled `lem:boring` (not `lem:local-age`
in this original source).

The strict source-aware repair script in this PR was applied successfully
and idempotently to that exact current file, then a small additional
review-only TODO was inserted at the I3 signature use.

- SHA-256 of the original `main.tex`:
  `493de0c377bc79ce956683c5905e342529e841d72a4e9d447a4cee14335cecd2`.
- SHA-256 of the resulting checked `main.tex`:
  `8f62d244faa24763d70faf5eb735ac04078349c10aefda6303f4510cb5bdd55d`.
- SHA-256 of the source-only Git application patch:
  `79cb7f64e508d605cdcb32e9d55060b174b62703f4af8dbe33243e0cdff8d126`.
- Local offline source-tree commit: `b25d2d9`, on repair branch
  `repair-v10-b3-common-socle-20261010`. The actual corrected source
  archive, exact `main.tex` and plain patch were provided as
  conversation attachments; they are **not** pushed to the Overleaf
  origin by this PR.
- `git diff --check` passed.
- The patch was applied to an independent archive extraction of the
  original source; the resulting `main.tex` checksum matched the
  repaired copy exactly.
- `pdflatex -interaction=nonstopmode -halt-on-error` completed and
  produced a 41-page preview; TeX syntax is valid. The environment did
  not have `bibtex`, so bibliography references in that preview remain
  unresolved.

**Mathematical scope:** The local finite common-socle age reduction,
neutral shape-map and B3 spacing obstruction have established Lean
proofs. This TeX source repair is NOT yet a kernel proof of the entire
non-neutral `lem:boring` shape-map or the global M2/M3 uses.
Moreover, the I3 signatures must be rebuilt from corrected finite
L-age witnesses, not the former impossible E-expanded upper-tail
condition.

The author's preceding four mathematical repairs outside the target
lemma/application caveats remain unchanged.
