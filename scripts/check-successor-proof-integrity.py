#!/usr/bin/env python3
"""Reject admitted proofs and new axioms in the Lean successor source tree.

Scan actual Lean lexical code, not documentation/comment examples. Supports
nested block comments, line comments, and escaped/multiline string literals.
This supplements kernel builds and transitive #print axioms checks; it does
not validate mathematical equivalence to manuscript statements.
"""
from __future__ import annotations

from pathlib import Path
import argparse
import re

ROOT = Path(__file__).resolve().parents[1]
HOLES = re.compile(r"\b(?:sorryAx|sorry|admit)\b")
DECLARATIONS = re.compile(
    r"(?m)^\s*(?:@\[[^\]\n]*\]\s*)*"
    r"(?:(?:private|protected|scoped|noncomputable|unsafe)\s+)*"
    r"(?:axiom|constant)\b"
)


def erase_comments_and_strings(text: str) -> str:
    """Mask non-code text with spaces, retaining line breaks and positions."""
    out = []
    i = 0
    depth = 0
    mode = "code"
    while i < len(text):
        c = text[i]
        nxt = text[i:i + 2]
        if mode == "code":
            if nxt == "--":
                out.extend("  ")
                i += 2
                mode = "line"
            elif nxt == "/-":
                out.extend("  ")
                i += 2
                mode = "block"
                depth = 1
            elif c == '"':
                out.append(" ")
                i += 1
                mode = "string"
            else:
                out.append(c)
                i += 1
        elif mode == "line":
            if c == "\n":
                out.append("\n")
                mode = "code"
            else:
                out.append(" ")
            i += 1
        elif mode == "block":
            if nxt == "/-":
                out.extend("  ")
                depth += 1
                i += 2
            elif nxt == "-/":
                out.extend("  ")
                depth -= 1
                i += 2
                if depth == 0:
                    mode = "code"
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif mode == "string":
            if c == "\\" and i + 1 < len(text):
                out.extend("\n" if ch == "\n" else " " for ch in text[i:i + 2])
                i += 2
            elif c == '"':
                out.append(" ")
                i += 1
                mode = "code"
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
    if mode == "block":
        raise ValueError("unterminated nested block comment")
    if mode == "string":
        raise ValueError("unterminated string literal")
    return "".join(out)


def findings(text: str) -> list[tuple[int, str]]:
    code = erase_comments_and_strings(text)
    matches = [(m.start(), m.group()) for pattern in (HOLES, DECLARATIONS)
               for m in pattern.finditer(code)]
    return [(code.count("\n", 0, pos) + 1, item.strip())
            for pos, item in sorted(matches)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=ROOT)
    args = parser.parse_args()
    root = args.source_root
    files = [root / "SuccessorTree.lean", *(root / "SuccessorTree").rglob("*.lean")]
    failures = []
    for file in files:
        if not file.is_file():
            failures.append(f"missing Lean source {file}")
            continue
        try:
            for line, word in findings(file.read_text(encoding="utf-8")):
                failures.append(f"{file.relative_to(root)}:{line}: {word}")
        except ValueError as error:
            failures.append(f"{file.relative_to(root)}: {error}")
    if failures:
        raise SystemExit("FAIL: whole-source proof-integrity audit:\n" +
                         "\n".join(failures))
    print(f"PASS: {len(files)} Lean source files contain no untrusted "
          "admission or source axiom declaration")


if __name__ == "__main__":
    main()
