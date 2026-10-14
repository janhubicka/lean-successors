#!/usr/bin/env python3
"""Strict, idempotent patch for the boring extension lemma in current main.tex.

Only this labelled lemma and one incorrect downstream application sentence
are modified. The input is NEVER overwritten without --in-place.
Use --check first against the author's CURRENT V10 source.
"""
from __future__ import annotations
import argparse, difflib
from pathlib import Path

HERE=Path(__file__).resolve().parent
B3=(HERE/"v10-boring-b3-replacement.tex").read_text().strip()
AGE=(HERE/"v10-boring-age-proof-replacement.tex").read_text().strip()
SUCC=(HERE/"v10-boring-successor-proof-replacement.tex").read_text().strip()

def one(s: str, anchor: str) -> int:
    n=s.count(anchor)
    if n!=1:
        raise ValueError(f"Expected exactly one {anchor!r}, found {n}")
    return s.index(anchor)

def repair(s: str) -> str:
    labels=[l for l in (r"\label{lem:boring}",r"\label{lem:local-age}") if l in s]
    if len(labels)!=1:
        raise ValueError("Cannot identify unique boring-extension lemma label")
    start=one(s,labels[0])
    b3=one(s,r"\item\label{item:boringage}")
    if not start < b3 < s.find(r"\end{lemma}",start):
        raise ValueError("B3 item is outside the labelled lemma")
    if r"\type{S}_0\in S" not in s[b3:b3+1400]:
        end=s.find(r"\end{enumerate}",b3)
        if end<0 or end-b3>2000:
            raise ValueError("Unsafe B3 boundary")
        old=s[b3:end]
        if "For every partial structure" not in old or r"\typev^{\ell+1}_\pstr{A}" not in old:
            raise ValueError("B3 differs from expected source: do not guess an edit")
        s=s[:b3]+B3+"\n\t"+s[end:]
    old_age=r"By \ref{item:boringage} we have"
    if old_age in s:
        i=one(s,old_age)
        j=s.find("Similarly, for every",i)
        if j<0 or j-i>6500 or r"\ominus m" not in s[i:j]:
            raise ValueError("Changed age proof requires manual review")
        s=s[:i]+AGE+"\n\n\t"+s[j:]
    elif r"To verify that $\type{Q}\in\KFpt$" not in s:
        raise ValueError("Age proof cannot be recognized")
    old_succ=r"Similarly, for every $\type{T}\in \KFpt(\ell)$"
    if old_succ in s:
        i=one(s,old_succ)
        j=s.find(r"\end{proof}",i)
        if j<0 or j-i>6500 or r"\S(F(\type{T})" not in s[i:j]:
            raise ValueError("Changed successor proof requires manual review")
        s=s[:i]+SUCC+"\n"+s[j:]
    elif r"If $n=\ell-1$" not in s:
        raise ValueError("Successor verification cannot be recognized")
    for old,new in (
        (r"\typev_\type{Q}^\ell(i+1)=F(\type{S}).",
         r"\typev_\type{Q}^{\ell+1}(i+1)=F(\type{S})."),
        (r"Notice that we now have $\typev_\type{Q}(i+1)=F(\type{S}).$",
         r"Thus the complete type of $i+1$ over the first $\ell+1$ ordinary vertices is $F(\type{S})$."),
        ("we we put","we put"),
    ):
        if old in s:
            if s.count(old)!=1: raise ValueError("Ambiguous adjacent proof repair")
            s=s.replace(old,new)
    # The stronger corrected B3 is NOT proved by the old Lemma comp.
    old=(r"Since conditions~\ref{item:boringB2} and \ref{item:boringage} "
         r"follow by Lemma~\ref{lem:comp}, we can apply Lemma~"
         r"\ref{lem:boring} to obtain the desired function $F_2$.")
    new=(r"Condition~\ref{item:boringB2} follows from Lemma~\ref{lem:comp}. "
         r"The strengthened finite $L$-age condition~\ref{item:boringage} "
         r"is not a consequence of the third statement of Lemma~\ref{lem:comp} "
         r"as presently formulated; its verification for this $f$ is a separate "
         r"remaining obligation before Lemma~\ref{lem:boring} can yield $F_2$. "
         r"\todo[inline]{v10: Prove the corrected finite common-socle $L$-age "
         r"condition for the decomposition map; the former $E$-expanded "
         r"upper-tail condition is insufficient.}")
    if old in s:
        if s.count(old)!=1: raise ValueError("Ambiguous decomposition application")
        s=s.replace(old,new)
    elif "strengthened finite $L$-age condition" not in s:
        raise ValueError("Downstream application cannot be recognized")
    # Replace only the now-obsolete EXACT earlier validation note, leaving
    # any author-reworded TODO untouched for review.
    stale=(r"\todo[inline]{Stevo\v sek: The no-age-change premise is now "
           r"type-correct: its types are at level $\ell+1$, matching "
           r"$f[S]$, and the concluding avoidance uses $e\prime[F\prime]$. "
           r"This fixes the statement, but the simultaneous extension and "
           r"age argument still need the detailed verification specified "
           r"in the report.}")
    current=(r"\todo[inline]{v10: B3 now uses the finite common-socle "
             r"$L$-age condition. Its non-neutral global ShapeMap and the "
             r"M2/M3 applications still require independent validation.}")
    if stale in s:
        s=s.replace(stale,current)
    # The old "all assumptions are necessary" claim is not justified
    # for the strengthened finite B3; make the scope precise.
    necessity_old=(r"The following lemma shows that the assumptions of "
                   r"Lemma~\ref{lem:boring} can not be relaxed.")
    necessity_new=(r"The following lemma records necessary conditions "
                   r"on shape-preserving maps. Its third condition is "
                   r"weaker than the finite $L$-age hypothesis now used "
                   r"in Lemma~\ref{lem:boring}.")
    if necessity_old in s:
        s=s.replace(necessity_old,necessity_new)
    elif necessity_new not in s:
        raise ValueError("Necessary-condition scope sentence changed")

    # Duplication likewise needs its own repaired-B3 verification.
    duplication_old=(r"An application of Lemma~\ref{lem:boring} yields "
                     r"the desired function $F_m^n$.")
    duplication_new=(r"An application of Lemma~\ref{lem:boring} yields "
                     r"the desired function $F_m^n$ once the corrected "
                     r"finite $L$-age condition has been checked for "
                     r"this duplication. "
                     r"\todo[inline]{v10: Verify condition "
                     r"\ref{item:boringage} for duplication; the earlier "
                     r"$E$-expanded argument is insufficient.}")
    if duplication_old in s:
        s=s.replace(duplication_old,duplication_new)
    elif duplication_new not in s:
        raise ValueError("Duplication application sentence changed")
    return s

def main() -> None:
    p=argparse.ArgumentParser()
    p.add_argument("source",type=Path)
    p.add_argument("--output",type=Path)
    p.add_argument("--in-place",action="store_true")
    p.add_argument("--check",action="store_true")
    a=p.parse_args()
    if a.output and a.in_place:
        p.error("choose --output or --in-place")
    before=a.source.read_text(encoding="utf-8")
    after=repair(before)
    if repair(after)!=after:
        raise AssertionError("B3 repair is not idempotent")
    if a.check:
        print("PASS: corrected B3 and proof patch is applicable and idempotent")
        return
    target=a.source if a.in_place else a.output
    if target is None:
        p.error("choose --output, --in-place, or --check")
    target.parent.mkdir(parents=True,exist_ok=True)
    if a.in_place and after!=before:
        backup=a.source.with_suffix(a.source.suffix+".before-b3")
        if backup.exists(): raise FileExistsError(backup)
        backup.write_text(before,encoding="utf-8")
    target.write_text(after,encoding="utf-8")
    print("Wrote",target)
    print("".join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),
                   fromfile=str(a.source),tofile=str(target)))[:12000])

if __name__=="__main__":
    main()
