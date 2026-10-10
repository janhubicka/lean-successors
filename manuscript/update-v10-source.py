#!/usr/bin/env python3
"""Apply the cumulative successor-v10 validation notes to *real* main.tex.

The author's four mathematical proof repairs are never edited. Review marks
are keyed by existing TeX labels. The script only replaces its own prior
markers, and legacy notes with the exact marker '% v10 validation note LABEL'.
It requires unique anchors, tests git-apply in a temporary checkout, checks
idempotence, and emits an unmodified-proof-content fingerprint.

Usage:
  python3 manuscript/update-v10-source.py /source/v10/main.tex --output /tmp/v10-review
  git -C /source/v10 apply --check /tmp/v10-review/v10-validated-notes.patch
  git -C /source/v10 apply /tmp/v10-review/v10-validated-notes.patch
The script never writes back into the input checkout.
"""
from __future__ import annotations
import argparse, difflib, hashlib, json, re, subprocess, tempfile
from pathlib import Path

OVERLAY = Path(__file__).with_name("v10-cumulative-validation-status.tex")
PREFIX = "successor-v10-proof"
# The exact label strings are from the latest recovered source patches.
# Definitions without a reliable TeX label are deliberately not guessed.
LABELS = {
    "obs:H": 2,                 # exact H+ interpretation
    "lem:meets": 3,             # charged meets
    "obs:signature-unique": 4,  # age-signature splicing
    "prob:upperbound": 5,       # final bound
}
OPTIONAL_LABELS = {
    "obs:env1": 0,             # admissible Kpt and concrete original pool
    "thm:zucker": 6,           # retained language-normalization boundary
    "cor:meet-origins": 7,     # checked iterated-closure generation budget
    "lem:local-age": 8,        # finite insertion and age test; global ShapeMap still open
}

def find_todos(tex: str) -> list[str]:
    """Extract inline TODOS in source order, respecting balanced TeX braces."""
    found = []
    for m in re.finditer(r"\\todo\[inline\]\{", tex):
        pos = m.end(); depth = 1
        while pos < len(tex):
            c = tex[pos]
            if c == "\\":
                pos += 2
                continue
            if c == "{": depth += 1
            if c == "}":
                depth -= 1
                if depth == 0:
                    found.append(tex[m.start():pos+1])
                    break
            pos += 1
        else:
            raise ValueError("Unterminated \\todo[inline] in overlay")
    if len(found) != 9:
        raise ValueError(f"Expected 9 grouped TODOs; found {len(found)}")
    return found

def uncommented_line(line: str) -> str:
    """Return the prefix before an unescaped TeX comment marker."""
    for pos, char in enumerate(line):
        if char != "%":
            continue
        slash = pos - 1
        while slash >= 0 and line[slash] == "\\":
            slash -= 1
        if (pos - slash - 1) % 2 == 0:
            return line[:pos]
    return line

def label_line_end(tex: str, label: str, optional=False) -> int | None:
    # Count occurrences, not just matching lines: duplicate labels on one
    # line must fail closed too. Keep the insertion at the end of its line.
    pattern = re.compile(r"\\label\{" + re.escape(label) + r"\}")
    matches = []
    offset = 0
    for line in tex.splitlines(keepends=True):
        for _ in pattern.finditer(uncommented_line(line)):
            if not line.endswith("\n"):
                raise ValueError(f"Label {label} has no terminating line break")
            matches.append(offset + len(line))
        offset += len(line)
    if not matches and optional:
        return None
    if len(matches) != 1:
        raise ValueError(f"Expected one uncommented label {label}, found {len(matches)}")
    return matches[0]

def skip_balanced_todo(tex: str, start: int) -> int:
    m = re.match(r"[ \t]*\\todo\[inline\]\{",tex[start:])
    if not m: raise ValueError("Malformed existing machine-labelled TODO")
    pos = start+m.end(); depth=1
    while pos < len(tex):
        c=tex[pos]
        if c=="\\": pos+=2; continue
        if c=="{": depth+=1
        if c=="}":
            depth-=1
            if depth==0:
                pos+=1
                if pos<len(tex) and tex[pos]=="\n": pos+=1
                return pos
        pos+=1
    raise ValueError("Unclosed existing machine-labelled TODO")

def remove_only_managed(tex: str) -> str:
    """Drop only markers about to be replaced, preserving every proof token."""
    anchors=set(LABELS)|set(OPTIONAL_LABELS)|{"definition-6-30"}
    # Legacy notes are removed only at matching anchors, never elsewhere.
    r=re.compile(r"^[ \t]*% (?:(v10 validation note) |("
                 + re.escape(PREFIX) + r"):)([\w:.-]+)[^\n]*\n",re.M)
    offset=0
    while m:=r.search(tex,offset):
        key=m.group(3)
        if key not in anchors:
            offset=m.end()
            continue
        after=skip_balanced_todo(tex,m.end())
        tex=tex[:m.start()]+tex[after:]
        offset=m.start()
    return tex

def transform(src: str, todos: list[str]) -> tuple[str,list[str]]:
    original_prose=remove_only_managed(src)
    out=original_prose
    found=[]
    for label, index in {**LABELS, **OPTIONAL_LABELS}.items():
        point=label_line_end(out,label,optional=label in OPTIONAL_LABELS)
        if point is None:
            found.append(f"OPTIONAL NOT FOUND: {label}")
            continue
        note=(f"% {PREFIX}:{label}\n"+todos[index]+"\n")
        out=out[:point]+note+out[point:]
        found.append(label)
    # Use the exact first sentence of Definition 6.30 only if unambiguous.
    succ_pat = re.compile(
        r"\\begin\{definition\}(?:\[[^\]]*\])?"
        r"(?:\s*\\label\{[^}]+\})?\s*Given a partial type",
        re.S)
    matches=list(succ_pat.finditer(out))
    if len(matches)==1:
        line_end=out.find("\n",matches[0].start())
        if line_end<0:
            raise ValueError("Definition 6.30 has no line break")
        note=f"% {PREFIX}:definition-6-30\n"+todos[1]+"\n"
        out=out[:line_end+1]+note+out[line_end+1:]
        found.append("definition-6-30")
    else:
        found.append(f"OPTIONAL Definition 6.30 not placed: {len(matches)} matches")
    if remove_only_managed(out)!=original_prose:
        raise ValueError("Unintended mathematical/prose changes detected")
    return out,found

def patch(before: str, after: str) -> str:
    diff="".join(difflib.unified_diff(
        before.splitlines(keepends=True),after.splitlines(keepends=True),
        fromfile="a/main.tex",tofile="b/main.tex",n=4))
    return "diff --git a/main.tex b/main.tex\n"+diff if diff else ""

def check_patch(raw: str, modified: str, diff: str) -> None:
    if not diff: return
    with tempfile.TemporaryDirectory(prefix="successor-v10-apply-") as temp:
        root=Path(temp)
        (root/"main.tex").write_text(raw,encoding="utf-8")
        subprocess.run(["git","init","-q",str(root)],check=True)
        for extra in [["--check"],[]]:
            r=subprocess.run(["git","-C",str(root),"apply",*extra,"-"],
                             input=diff,text=True,capture_output=True)
            if r.returncode: raise ValueError(f"git apply {extra}: {r.stderr}")
        if (root/"main.tex").read_text(encoding="utf-8")!=modified:
            raise ValueError("git apply changed unexpected content")

def run(input_path: Path, output: Path):
    raw=input_path.read_text(encoding="utf-8")
    todos=find_todos(OVERLAY.read_text(encoding="utf-8"))
    changed,found=transform(raw,todos)
    twice,_=transform(changed,todos)
    if twice!=changed: raise ValueError("Idempotence failure")
    diff=patch(raw,changed)
    check_patch(raw,changed,diff)
    output.mkdir(parents=True,exist_ok=True)
    (output/"v10-validated-notes.patch").write_text(diff,encoding="utf-8")
    (output/"main.reviewed.tex").write_text(changed,encoding="utf-8")
    manifest={
        "input_sha256": hashlib.sha256(raw.encode()).hexdigest(),
        "updated_sha256": hashlib.sha256(changed.encode()).hexdigest(),
        "source_kind":"actual supplied main.tex",
        "unchanged_non_review_prose":True,
        "git_apply_check":"passed",
        "idempotence":"passed",
        "anchors":found,
        "changed":changed!=raw,
        "boundary":"Exact normalized Kpt/H, closure budget and finite local-age ingredients; global maps and final application open. Four repairs untouched."}
    (output/"MANIFEST.json").write_text(json.dumps(manifest,indent=2)+"\n")
    print(json.dumps(manifest,indent=2))

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("main",type=Path)
    p.add_argument("--output",type=Path,required=True)
    a=p.parse_args()
    run(a.main,a.output)
