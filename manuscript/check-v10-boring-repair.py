#!/usr/bin/env python3
"""Regression for source-safe mathematical B3 replacement."""
from pathlib import Path
import importlib.util
p=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location("repair",(p/"repair-v10-boring-lemma.py"))
assert spec is not None and spec.loader is not None
m=importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
old=(p/"v10-boring-old-fixture.tex").read_text()
new=m.repair(old)
assert new!=old
assert m.repair(new)==new
assert r"\item\label{item:boringage}" in new
assert r"\type{S}_0\in S" in new
assert r"\typev_\type{Q}^{\ell+1}" in new
assert r"If $n=\ell-1$" in new
assert r"strengthened finite $L$-age condition" in new
assert "% SENTINEL: never change this unrelated source" in new
assert new.count(r"\label{lem:boring}")==1
assert old.count(r"\label{item:boringage}")==new.count(r"\label{item:boringage}")
try:
    m.repair(old.replace(r"\label{item:boringage}",r"\label{item:other}"))
    raise AssertionError("Missing anchor did not fail closed")
except ValueError:
    pass
print("PASS: B3+proof repair source-safe, idempotent, and fail-closed")
