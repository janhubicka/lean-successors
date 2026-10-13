#!/usr/bin/env python3
"""Regression tests for the cumulative v10 M2 appendix insertion."""
from pathlib import Path
import importlib.util
import tempfile

here=Path(__file__).parent
spec=importlib.util.spec_from_file_location('m2_appender',here/'install-v10-m2-appendix.py')
mod=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

base=r'''\documentclass{article}
\usepackage{amsthm}
\begin{document}
\begin{theorem}\label{thm:m2}
Preserve this author theorem.
\end{theorem}
% Existing author corrections are frozen.
\end{document}
'''
with tempfile.TemporaryDirectory() as d:
    root=Path(d)
    main=root/'main.tex'
    main.write_text(base,encoding='utf-8')
    before,after,appendix,diff,exists=mod.prepare(main)
    assert not exists
    assert mod.INPUT_MARK in after and mod.INPUT_LINE in after
    assert after.count('\\appendix') == 1
    assert after.replace('\\appendix\n'+mod.INPUT_MARK+'\n'+mod.INPUT_LINE+'\n','',1)==base
    assert 'Preserve this author theorem.' in after
    assert mod.splice(after)==after
    mod.verify_patch(before,after,appendix,diff,exists)
    mod.run(main,root/'out')
    assert (root/'out'/'v10-m2-appendix.patch').read_text()==diff
    main.write_text(after,encoding='utf-8')
    target=root/mod.APPENDIX_REL
    target.parent.mkdir(exist_ok=True)
    target.write_text(appendix,encoding='utf-8')
    assert mod.prepare(main)[3]==''
    mod.run(main,root/'out2')
    assert (root/'out2'/'v10-m2-appendix.patch').read_text()==''
    already=base.replace(r'\begin{document}',r'\begin{document}'+'\n'+r'\appendix')
    assert mod.splice(already).count(r'\appendix')==1
    for broken in [
        base.replace(r'\end{document}',''),
        base.replace(r'\end{document}',r'\end{document}'+'\n'+r'\end{document'),
        base.replace(r'\end{document}',mod.INPUT_MARK+'\n'+r'\end{document}'),
        base.replace(r'\end{document}',mod.INPUT_LINE+'\n'+r'\end{document}'),
        base.replace(r'\end{document}',r'\appendix'+'\n'+r'\appendix'+'\n'+r'\end{document}'),
    ]:
        try: mod.splice(broken)
        except ValueError: pass
        else: raise AssertionError('Accepted ambiguous input: '+broken)
    target.write_text('DIFFERENT',encoding='utf-8')
    try: mod.prepare(main)
    except ValueError: pass
    else: raise AssertionError('Overwrote an existing different appendix')
print('PASS: author prose preserved, appendix inserted once, git patch applies, re-run no-op, ambiguous input rejected')
