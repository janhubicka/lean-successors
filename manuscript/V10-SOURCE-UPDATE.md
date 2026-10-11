# Updating successor-v10 manuscript validation

The cumulative author-facing status notes are in
[v10-cumulative-validation-status.tex](v10-cumulative-validation-status.tex).
They distinguish Lean-certified theorem components from bridges to the
paper's precise Kpt construction.

In an editable v10 Git checkout **already containing the four repaired
mathematical passages**, run the source-aware updater:

    python3 /path/to/lean-successors/manuscript/update-v10-source.py \
      /path/to/v10/main.tex --output /tmp/v10-reviewed
    git -C /path/to/v10 apply --check /tmp/v10-reviewed/v10-validated-notes.patch
    git -C /path/to/v10 apply /tmp/v10-reviewed/v10-validated-notes.patch

The updater writes a patch, an updated main.reviewed.tex and a manifest
pinning the input/output SHA-256. It verifies both git application in an
isolated repository and idempotence, and refuses ambiguous required
anchors. Previously machine-marked notes it owns are replaced.
Unmarked notes and mathematical proof text, including the four repairs,
remain unchanged. A separately tested fixture and fast GitHub Actions
workflow verify the updater.

**The original editable main.tex was not directly modified in this
repository.** The previous TGZ archive is visible in the user's Library,
but its raw bytes could not be materialized in this runtime. A source
patch against those unavailable bytes must not be fabricated from a PDF.

## Remaining theorem boundary

The normalized finite unary/binary Kpt tree/meet is checked, together
with the E3 no-new-tuples consequence. The predecessor, canonical
parameter and terminal Sigma-letter extraction and one-step
uniqueness are being formalized separately.

The exact forward successor, admissibility of terminal Sigma letters,
S3 cover realization, the concrete monoid M1--M3, and the final
big-Ramsey upper-bound application still require proof. A conditional
Lean theorem is not a GREEN marker for the unqualified manuscript
proposition. Do not combine old individual TODO patches with the new
cumulative updater; it already handles the machine-labelled notes
that it owns.
