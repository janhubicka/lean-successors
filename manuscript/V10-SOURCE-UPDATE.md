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

## M2 non-edge appendix (13 October 2026)

The separate author-requested English proof is tracked in
[v10-m2-nonedge-appendix.tex](v10-m2-nonedge-appendix.tex).
It keeps the M2 argument outside the frozen original proof, with labelled
lemmas for complete-record recovery, simultaneous image transport,
compatibility, and the finite forbidden-age test. Its conclusion is the
one-gap M2 factorization using the existing global compatible boring
extension theorem. **This is an English proof under Lean review, not an
M2 GREEN validation marker.**

The actual editable main.tex is still external to lean-successors.
To install the tracked appendix into an editable v10 checkout, run:

    python3 /path/to/lean-successors/manuscript/install-v10-m2-appendix.py \
      /path/to/v10/main.tex --output /tmp/v10-m2-appendix
    git -C /path/to/v10 apply --check /tmp/v10-m2-appendix/v10-m2-appendix.patch
    git -C /path/to/v10 apply /tmp/v10-m2-appendix/v10-m2-appendix.patch

The generated patch adds appendices/v10-m2-nonedge.tex and inserts a
single \input{appendices/v10-m2-nonedge} before \end{document}.
It inserts \appendix only if no uncommented appendix switch is present,
rejects ambiguous insertion points or conflicting appendix content,
retains all existing author mathematical prose byte-for-byte, and is
idempotent. This installer can be used after the independent validation
note updater; do not replace the author main.tex with a reconstructed
copy or annotate M2 GREEN before the final Lean endpoint is audited.
The exact original v10 archive is not in this checked repository, so a
patch against it has not been asserted as applied.

Regression: python3 manuscript/check-v10-m2-appendix.py.
