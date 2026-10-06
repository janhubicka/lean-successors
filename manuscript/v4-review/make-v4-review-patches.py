#!/usr/bin/env python3
"""Generate review-only manuscript patches without modifying the source tree.

Exact mode reads the user's archive/tree and tests the resulting patches against
those exact bytes. Reference mode uses only the v4 anchor contexts recovered in
the conversation; its manifest explicitly records this weaker validation.
"""
from __future__ import annotations

import argparse
import difflib
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile

HELPER = "fat-tree-validation-v4.tex"
FAT_THEOREM = r"\begin{theorem}[Ellentuck theorem for fat subtrees]"
ABSTRACT = r"\begin{theorem}[Todorcevic's Abstract Ellentuck theorem~\cite{todorcevic2010introduction}]\label{thm:stevo}"
STRUCTURAL = r"\begin{proof}[Proof of Theorem~\ref{thm:fatramseyspace}]"
FINAL_A4 = r"\begin{proof}[Proof of Proposition~\ref{prop:A4}]"
PATCH_NAMES = [
    "0001-isolated-fat-tree-validation-overlay.patch",
    "0002-abstract-and-structural-review.patch",
    "0003-a4-all-trace-fusion-and-coverage-review.patch",
]


def reference_main() -> str:
    # Adjacent lines below were read from the attached v4 main.tex. Padding is
    # deliberately synthetic and is never included in a one-context-line hunk.
    snippets = [
        "Again, we can establish an Ellentuck-type theorem.\n" + FAT_THEOREM +
        "\n\t" + r"\label{thm:fatramseyspace}" + "\n",
        r"To prove Theorem~\ref{thm:fatramseyspace} we will apply the following theorem." +
        "\n" + ABSTRACT + "\n",
        r"\begin{prop}[\ref{item:A4} pigeonhole]" + "\n\t" + r"\label{prop:A4}" +
        "\n\t" + r"For every $\fat{x}\in \mathcal {AR}$ and $\fat{U}\in \mathcal {R}$ such that $\depth_\fat{U}(\fat{x})< \omega$ and every $\mathcal O\subseteq \mathcal{AR}_{|\fat x|+1}$" + "\n",
        STRUCTURAL + "\n\t" + r"In order to apply Theorem~\ref{thm:stevo} we only need to verify axioms \ref{item:A1}, \ref{item:A2}, \ref{item:A3} and \ref{item:A4}." + "\n",
        r"\begin{lemma}" + "\n\t" + r"\label{lem:fixlevel}" + "\n" +
        r"\todo[inline]{Stevo\v sek: The inductive survival invariant must be stated relative to the current thinning, not an earlier ambient fat tree. More importantly, this lemma still depends on the unresolved fat-line pigeonhole lemma. A complete repair must also prove that the final fusion captures every finite one-level extension, not merely the choices enumerated at an intermediate stage.}" + "\n",
        FINAL_A4 + "\n\t" + r"Let $\fat{U}$, $\fat{x}$ and $\mathcal O$ be as in the statement of the proposition." + "\n",
    ]
    return "\n" * 200 + ("\n" * 40).join(snippets) + "\n" * 40


def insert_line(text: str, anchor: str, addition: str, *, before: bool = False) -> str:
    lines = text.splitlines(keepends=True)
    positions = [i for i, line in enumerate(lines) if line.strip() == anchor.strip()]
    if len(positions) != 1:
        raise ValueError(f"Expected one uncommented anchor {anchor!r}; found {len(positions)}")
    position = positions[0] + (0 if before else 1)
    lines.insert(position, addition + "\n")
    return "".join(lines)


def diff(old: dict[str, str], new: dict[str, str], context: int) -> str:
    result: list[str] = []
    for name in sorted(set(old) | set(new)):
        a, b = old.get(name, ""), new.get(name, "")
        if a == b:
            continue
        result.append(f"diff --git a/{name} b/{name}\n")
        if name not in old:
            result.append("new file mode 100644\n")
        result.extend(difflib.unified_diff(
            a.splitlines(keepends=True), b.splitlines(keepends=True),
            fromfile=f"a/{name}" if name in old else "/dev/null",
            tofile=f"b/{name}", n=context,
        ))
    return "".join(result)


def check_patches(initial: dict[str, str], final: dict[str, str], patches: list[Path]) -> None:
    with tempfile.TemporaryDirectory(prefix="v4-patch-check-") as folder:
        root = Path(folder)
        subprocess.run(["git", "init", "-q", folder], check=True)
        for name, content in initial.items():
            (root / name).write_text(content, encoding="utf-8")
        for patch in patches:
            subprocess.run(["git", "-C", folder, "apply", "--check", str(patch.resolve())], check=True)
            subprocess.run(["git", "-C", folder, "apply", str(patch.resolve())], check=True)
        for name, expected in final.items():
            actual = (root / name).read_text(encoding="utf-8")
            if actual != expected:
                raise AssertionError(f"Round-trip mismatch in {name}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--archive", type=Path)
    modes.add_argument("--source-tree", type=Path)
    modes.add_argument("--reference", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if shutil.which("git") is None:
        parser.error("git is required for patch application checks")
    helper = Path(__file__).with_name(HELPER).read_text(encoding="utf-8")
    metadata: dict[str, object] = {}
    if args.archive:
        with tarfile.open(args.archive, "r:gz") as archive:
            members = [m for m in archive.getmembers()
                       if m.isfile() and (m.name == "main.tex" or m.name.endswith("/main.tex"))]
            if len(members) != 1 or members[0].size > 20 * 1024 * 1024:
                parser.error("archive must contain one bounded regular main.tex file")
            stream = archive.extractfile(members[0])
            assert stream is not None
            main_text = stream.read().decode("utf-8")
        metadata["input_archive_sha256"] = hashlib.sha256(args.archive.read_bytes()).hexdigest()
        mode = "exact attached archive/tree bytes"
    elif args.source_tree:
        main_text = (args.source_tree / "main.tex").read_text(encoding="utf-8")
        mode = "exact attached archive/tree bytes"
    else:
        main_text = reference_main()
        mode = "recovered v4 anchor contexts only; NOT a full uploaded-archive check"
    if r"\input{fat-tree-validation-v4.tex}" in main_text:
        parser.error("the v4 overlay is already loaded; refusing duplicate application")
    out = args.output.resolve()
    if out.exists() and any(out.iterdir()):
        parser.error("output directory must be absent or empty")
    out.mkdir(parents=True, exist_ok=True)
    states = [{"main.tex": main_text}]
    stage = dict(states[-1])
    stage[HELPER] = helper
    stage["main.tex"] = insert_line(stage["main.tex"], FAT_THEOREM,
        r"\input{fat-tree-validation-v4.tex}", before=True)
    states.append(stage)
    stage = dict(states[-1])
    stage["main.tex"] = insert_line(stage["main.tex"], FAT_THEOREM,
        r"\fatvfourTheoremReview", before=True)
    stage["main.tex"] = insert_line(stage["main.tex"], ABSTRACT,
        r"\fatvfourAbstractReview", before=True)
    stage["main.tex"] = insert_line(stage["main.tex"], STRUCTURAL,
        r"\fatvfourStructuralReview")
    states.append(stage)
    stage = dict(states[-1])
    stage["main.tex"] = insert_line(stage["main.tex"], r"\label{prop:A4}",
        r"\fatvfourAfourReview")
    stage["main.tex"] = insert_line(stage["main.tex"], r"\label{lem:fixlevel}",
        r"\fatvfourFusionReview")
    stage["main.tex"] = insert_line(stage["main.tex"], FINAL_A4,
        r"\fatvfourCoverageReview")
    states.append(stage)
    context = 1 if args.reference else 3
    for i, name in enumerate(PATCH_NAMES):
        (out / name).write_text(diff(states[i], states[i + 1], context), encoding="utf-8")
    (out / "combined.patch").write_text(diff(states[0], states[-1], context), encoding="utf-8")
    check_patches(states[0], states[-1], [out / n for n in PATCH_NAMES])
    check_patches(states[0], states[-1], [out / "combined.patch"])
    # Regression: context-based application must tolerate shifted line numbers.
    shifted0 = {"main.tex": "% shifted-context regression\n" * 83 + main_text}
    shifted1 = dict(states[-1])
    shifted1["main.tex"] = "% shifted-context regression\n" * 83 + states[-1]["main.tex"]
    check_patches(shifted0, shifted1, [out / "combined.patch"])
    metadata.update({
        "input_mode": mode,
        "observed_uploaded_git_head": "c4959f5",
        "input_main_sha256": hashlib.sha256(main_text.encode()).hexdigest(),
        "lean_checkpoint": "215baad75a57b43967063b8d33ed8e6989125501",
        "lean_actions_run": 37383862698,
        "lean_full_build_run": 37383862703,
        "abstract_checkpoint": "bdb601607c03a945bbcd01cfccaa884d4c95e69f",
        "abstract_actions_run": 37365422442,
        "patches": PATCH_NAMES,
        "patch_checks": "sequential, combined, and shifted-context round trips passed for the stated input mode",
        "scope": "validation markers and TODO notes only; original manuscript prose is preserved",
        "full_manuscript_latex_build": "not performed",
        "general_fat_tree_ellentuck": "fully formalized; unconditional fixed-stem A4 and Ellentuck endpoint audited",
    })
    (out / "manifest.json").write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
    shutil.copy2(Path(__file__), out / Path(__file__).name)
    (out / HELPER).write_text(helper, encoding="utf-8")
    (out / "README.txt").write_text(
        "SUCCESSORS V4 — VALIDATION AND CORRECTION-NOTE PATCHES\n\n"
        "These patches pin the completed, audited fat-tree A4/Ellentuck proof.\n"
        "Apply from the root of your extracted successors Git tree:\n\n"
        "  git apply --check /path/to/package/combined.patch\n"
        "  git apply /path/to/package/combined.patch\n\n"
        "Alternatively apply the three numbered patches in order, not both forms.\n"
        "The existing validation.tex and all original prose remain unchanged.\n\n"
        "The prebuilt package was checked using recovered v4 anchor contexts, not\n"
        "by a full application to the uploaded archive. For an exact-source check\n"
        "and regenerated patches, run (Python 3.10+ and Git are required):\n\n"
        "  python3 make-v4-review-patches.py --archive /path/to/sucessors-v4.tgz --output /tmp/v4-exact-patches\n\n"
        "or use --source-tree /path/to/successors instead of --archive. The script\n"
        "reads the source, generates patches and tests them in a temporary Git\n"
        "repository; it does not modify or commit your source tree. Output must\n"
        "be a new or empty directory. Read manifest.json for the actual check mode.\n\n"
        "The focused successor audit has 71 theorem-axiom reports and the full\n"
        "successor build passes. The abstract library post-merge audit passes too.\n"
        "The geometric fixed-stem pigeonhole theorem and fat-tree Ellentuck endpoint\n"
        "are unconditional at the pinned checkpoint.\n",
        encoding="utf-8",
    )
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
