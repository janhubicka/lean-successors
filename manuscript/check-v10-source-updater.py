#!/usr/bin/env python3
"""Regression test for source-aware successor-v10 annotation patches."""
import importlib.util
from pathlib import Path
import tempfile

root=Path(__file__).parent
spec=importlib.util.spec_from_file_location("v10_updater", root/"update-v10-source.py")
app=importlib.util.module_from_spec(spec)
spec.loader.exec_module(app)

old=r"""\documentclass{article}
\usepackage{todonotes}
\begin{document}
\begin{theorem}\label{thm:zucker}
Old theorem remains unchanged.
\end{theorem}
\begin{observation}\label{obs:H}
Old H-model prose is unchanged.
\end{observation}
\begin{observation}\label{obs:env1}
Old parameter closure discussion.
\end{observation}
\begin{lemma}\label{lem:meets}
% v10 validation note lem:meets
\todo[inline]{Former robot note with nested \texttt{command}.}
% v10 repair 2: do not touch the mathematical statement
Original mixed-generation formula.
\end{lemma}
\begin{corollary}\label{cor:meet-origins}
% v10 validation note cor:meet-origins
\todo[inline]{Stale iterated-meet conditional note.}
The meet bound follows conditionally.
\end{corollary}
\begin{lemma}\label{lem:local-age}
Another local age lemma.
\end{lemma}
\begin{observation}\label{obs:signature-unique}
Original signature formula.
\end{observation}
\begin{lemma}\label{lem:signatures}
Original relocation proof.
\end{lemma}
\begin{prop}\label{prob:upperbound}
The four reconstructed repairs remain unchanged.
\end{prop}
\begin{definition}
Given a partial type $T^+$, define its successor as prescribed.
\end{definition}
% v10 validation note claim:boring
\todo[inline]{Other old review notes must NOT be deleted.}
\end{document}
"""
todos=app.find_todos(app.OVERLAY.read_text(encoding="utf-8"))
assert len(todos)==8
once,markers=app.transform(old,todos)
twice,_=app.transform(once,todos)
assert once==twice
assert "Former robot note" not in once
assert "Stale iterated-meet conditional note" not in once
assert "% successor-v10-proof:cor:meet-origins" in once
assert "% successor-v10-proof:thm:zucker" in once
assert "% v10 repair 2: do not touch" in once
assert "Original mixed-generation formula" in once
assert "Other old review notes must NOT be deleted" in once
assert "% successor-v10-proof:lem:meets" in once
assert len(markers)==8
assert "% successor-v10-proof:definition-6-30" in once
assert app.remove_only_managed(once)==app.remove_only_managed(old)
with tempfile.TemporaryDirectory() as tmp:
    path=Path(tmp)
    main=path/"main.tex"
    main.write_text(old,encoding="utf-8")
    app.run(main,path/"review")
    patch=(path/"review"/"v10-validated-notes.patch").read_text()
    assert patch.startswith("diff --git a/main.tex b/main.tex")
    assert (path/"review"/"main.reviewed.tex").read_text()==once
    app.run(path/"review"/"main.reviewed.tex",path/"twice")
    assert (path/"twice"/"v10-validated-notes.patch").read_text()==""
print("PASS: anchored v10 proof notes preserve all unmarked prose; idempotent; git apply")

# Fail closed on ambiguous or absent required anchors and malformed notes.
for bad in [
    old.replace(r"\label{lem:meets}", r"\label{lem:meets}\label{lem:meets}"),
    old.replace(r"\label{lem:meets}", ""),
    old.replace(r"\label{lem:meets}", "\\label{lem:meets}\n\\label{lem:meets}"),
    old.replace(r"\todo[inline]{Former robot note with nested \texttt{command}.}", r"\todo[inline]{unfinished"),
]:
    try:
        app.transform(bad, todos)
    except ValueError:
        pass
    else:
        raise AssertionError("Invalid input was accepted")
print("PASS: required-anchor and malformed-note negative tests")

# Labels after real comments do not count; escaped percent is ordinary text.
assert app.transform("% ignored \\label{lem:meets}\n"+old, todos)[0].endswith(once)
assert app.label_line_end("escaped \\% \\label{only}\n", "only") is not None
assert app.label_line_end("comment % \\label{only}\n", "only", optional=True) is None
print("PASS: duplicate labels on one line and TeX-comment anchor handling")
