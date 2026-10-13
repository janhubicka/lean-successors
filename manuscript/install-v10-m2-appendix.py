#!/usr/bin/env python3
r"""Safely add the separate M2 proof appendix to an editable v10 main.tex.

This is deliberately independent of the cumulative validation-note updater.
It leaves every existing author paragraph unchanged, inserts one \input at
\end{document}, and carries the appendix source as a separate tracked file.
It emits a git-applicable patch but never mutates the supplied checkout.
"""
from __future__ import annotations

import argparse
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

APPENDIX_REL = Path('appendices/v10-m2-nonedge.tex')
APPENDIX_SOURCE = Path(__file__).with_name('v10-m2-nonedge-appendix.tex')
INPUT_MARK = '% successor-v10-m2-appendix-input'
INPUT_LINE = r'\input{appendices/v10-m2-nonedge}'


def uncommented(line: str) -> str:
    for i, c in enumerate(line):
        if c != '%':
            continue
        prev = i - 1
        while prev >= 0 and line[prev] == '\\':
            prev -= 1
        if (i - prev - 1) % 2 == 0:
            return line[:i]
    return line


def noncommented_count(source: str, target: str) -> int:
    return sum(line.count(target) for line in
               (uncommented(line) for line in source.splitlines()))


def splice(source: str) -> str:
    r"""Insert exactly one \input, with \appendix only if not already present."""
    count = noncommented_count(source, INPUT_LINE)
    if count > 1:
        raise ValueError('M2 appendix is included more than once')
    count_end = noncommented_count(source, r'\end{document}')
    if count_end != 1:
        raise ValueError(f'Expected one uncommented end{{document}}, found {count_end}')
    if count == 1:
        if source.count(INPUT_MARK) != 1:
            raise ValueError('M2 appendix already included without our marker')
        return source
    if INPUT_MARK in source:
        raise ValueError('Orphaned M2 appendix marker')
    append_switch = noncommented_count(source, r'\appendix')
    if append_switch > 1:
        raise ValueError('Multiple appendix switches: insertion point ambiguous')
    addition = ('' if append_switch else '\\appendix\n') + INPUT_MARK + '\n' + INPUT_LINE + '\n'
    lines = source.splitlines(keepends=True)
    end_lines = [i for i, line in enumerate(lines) if r'\end{document}' in uncommented(line)]
    if len(end_lines) != 1:
        raise ValueError('Ambiguous end-of-document line')
    index = end_lines[0]
    if not re.match(r'^\s*\\end\{document\}\s*(?:%.*)?$', lines[index].rstrip('\n')):
        raise ValueError('end{document} must occupy its own line')
    lines[index:index] = [addition]
    result = ''.join(lines)
    if result.replace(addition, '', 1) != source:
        raise ValueError('Proof prose preservation check failed')
    return result


def unified_diff(before: str, after: str, old_name: str, new_name: str, is_new=False) -> str:
    if before == after:
        return ''
    lhs = '/dev/null' if is_new else 'a/' + old_name
    rhs = 'b/' + new_name
    return 'diff --git a/' + old_name + ' b/' + new_name + '\n' + ('new file mode 100644\n' if is_new else '') + ''.join(
        difflib.unified_diff(before.splitlines(keepends=True), after.splitlines(keepends=True),
                             fromfile=lhs, tofile=rhs, n=3))


def prepare(main: Path):
    source = main.read_text(encoding='utf-8')
    appendix = APPENDIX_SOURCE.read_text(encoding='utf-8')
    target = main.parent / APPENDIX_REL
    previous = target.read_text(encoding='utf-8') if target.exists() else ''
    if previous and previous != appendix:
        raise ValueError(f'Existing appendix differs: {target}')
    after = splice(source)
    if splice(after) != after:
        raise ValueError('Repeated insertion is not idempotent')
    diff = unified_diff(source, after, 'main.tex', 'main.tex')
    if not target.exists():
        diff += unified_diff('', appendix, str(APPENDIX_REL), str(APPENDIX_REL), True)
    return source, after, appendix, diff, target.exists()


def verify_patch(source: str, after: str, appendix: str, diff: str, already_exists: bool):
    with tempfile.TemporaryDirectory(prefix='v10-m2-appendix-') as d:
        root = Path(d)
        (root/'main.tex').write_text(source, encoding='utf-8')
        if already_exists:
            dest = root/APPENDIX_REL
            dest.parent.mkdir(parents=True)
            dest.write_text(appendix, encoding='utf-8')
        subprocess.run(['git','init','-q',str(root)],check=True)
        if diff:
            for args in (['--check'], []):
                p = subprocess.run(['git','-C',str(root),'apply',*args,'-'],
                                   input=diff,capture_output=True,text=True)
                if p.returncode:
                    raise ValueError('git apply ' + ' '.join(args) + ': ' + p.stderr)
        if (root/'main.tex').read_text(encoding='utf-8') != after:
            raise ValueError('Patched main.tex does not match verified splice')
        if (root/APPENDIX_REL).read_text(encoding='utf-8') != appendix:
            raise ValueError('Patched appendix does not match tracked source')


def run(main: Path, output: Path):
    if main.name != 'main.tex':
        raise ValueError('Expect the actual editable main.tex, not a PDF or reconstructed copy')
    source, after, appendix, diff, existing = prepare(main)
    verify_patch(source, after, appendix, diff, existing)
    output.mkdir(parents=True, exist_ok=True)
    (output/'v10-m2-appendix.patch').write_text(diff, encoding='utf-8')
    (output/'main.with-m2-appendix.tex').write_text(after, encoding='utf-8')
    appendix_out = output/APPENDIX_REL
    appendix_out.parent.mkdir(parents=True,exist_ok=True)
    appendix_out.write_text(appendix, encoding='utf-8')
    manifest = {
        'input_sha256': hashlib.sha256(source.encode()).hexdigest(),
        'output_sha256': hashlib.sha256(after.encode()).hexdigest(),
        'appendix_sha256': hashlib.sha256(appendix.encode()).hexdigest(),
        'appendix_path': str(APPENDIX_REL),
        'proof_prose_unchanged': True,
        'git_apply_check': 'passed',
        'idempotence': 'passed',
        'changed': bool(diff),
        'lean_status': 'M2 OPEN pending complete Lean/axiom audit'
    }
    (output/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(manifest,indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('main',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    run(args.main,args.output)
