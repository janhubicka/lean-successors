# Localized successor-manuscript annotations

The mathematical proof is pinned to Lean commit
`1856f22fa1c94a27b3b282945da7d0f962903cc6`, which passed the build,
interface regressions and eight transitive axiom checks in
[Actions run 37150740752](https://github.com/janhubicka/lean-successors/actions/runs/37150740752).

**The uploaded `successor-clean(2).tgz` was not opened:** the local runtime
failed. The pre-generated patches use only label-adjacent contexts recovered
from an older `main.tex`. They add annotations without replacing existing
prose. A full compilation or byte-for-byte comparison with the uploaded draft
has not been performed. The generator can instead read the exact current
checkout and construct checked patches against it.

## Generate against the actual TeX checkout

Use Python 3 and Git. No Python packages or network access are needed.
Keep `make-validation-patches.py` and `successor-validation.tex` together.
For example, after extracting the proof-audit artifact:

```sh
python3 /path/to/proof-audit/manuscript/make-validation-patches.py \
  --root /path/to/successor-tex \
  --output /tmp/successor-tex-annotations
```

The input directory is not modified. Every patch is tested with
`git apply --check` and then applied in an isolated temporary checkout.
The generator checks that the resulting files are exactly as intended and
that a repeated run does not duplicate markers or notes. A missing or duplicate
uncommented label causes a clear failure rather than a guessed insertion.
The default main file is `main.tex`; another relative path can be passed with
`--main`.

Then, from the TeX checkout, use the combined patch:

```sh
git apply --check /tmp/successor-tex-annotations/all-annotations.patch
git apply /tmp/successor-tex-annotations/all-annotations.patch
git diff --check
git diff --stat
```

Alternatively, apply the numbered patches in order for separate commits.
**Do not apply both the combined patch and the numbered series.** The
`MANIFEST.json` records the exact generator mode and input-main SHA-256.
Use a fresh output directory for each generation.

## Pre-generated reference-context patches

The workflow's `manuscript-patches/` directory contains the same annotation
set generated with `--reference`. Its manifest explicitly says that this was
not checked against the uploaded archive. It is tested against the recovered
contexts and against shifted copies of those contexts. Start with
`git apply --check` on the actual draft; regenerate with `--root` when necessary.

The seven patches add the validation overlay, then annotate canonical
extension, fixed-prefix factorization, local replay scope, the one-moving-level
theorem, the finite-dimensional theorem, and the formal-interface boundary.
The finite-dimensional marker is beside the proof headed by
`thm:shaperamseyN`; the separate statement file `nthm.tex` was not recovered
and is not guessed or overwritten.

## Markers and review notes

`successor-validation.tex` reuses an existing `validation.tex` when available
and supplies compatible fallback macros otherwise. Its local wrappers pin
successor links without changing the repository or revision used by other
validation markers. Green means the indicated theorem is covered; orange
means only the specified core or representation is covered; blue records an
interface boundary.

All new inline notes begin `Řehořek:` and are guarded by `\ifshowvalidation`.
For a circulation copy, put this after the overlay is loaded:

```tex
\showvalidationfalse
```

The annotations do not certify the fat-tree Ramsey-space or topological
transfer arguments, application-specific statements, or envelope bounds.
Existing todos on those topics remain untouched.

## Lean patches in the same artifact

`shape-ramsey-completion.patch` belongs in `lean-successors`, not the TeX tree.
Its base is recorded in `COMPLETION_BASE`; `shape-ramsey-branch.patch` has the
separate base recorded in `BRANCH_BASE`. The artifact also contains the tested
commit, toolchain, resolved Lake manifest, build log, axiom log, and checksums.
Choose the matching base and run `git apply --check` before applying either.
These are plain diffs for `git apply`, not mail patches for `git am`.
