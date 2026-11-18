#!/usr/bin/env python3
"""Split the six-iteration enemy loop into independently checkable regions.

Usage: play_enemy_segments.py ENEMY.cfg TAIL.cfg OUTDIR
The front covers AF01..AF05; Ei covers iteration i until AF0B; Mi executes
INX/CPX/branch/STX to the next iteration or tail. No iteration is omitted.
All original contract hypotheses and exceptional exits are retained.
"""
import sys
from pathlib import Path
source, tail, out = map(Path, sys.argv[1:])
lines = source.read_text().splitlines()
base = [l for l in lines if not l.startswith(('entry ', 'next ', 'saveg ', 'x ')) and l != 'exit AF10']
out.mkdir(parents=True, exist_ok=True)
def emit(name, pc, end, next_path, extra=()):
    cfg = [f'entry {pc} F9', f'exit {end}'] + base + list(extra)
    cfg += [f'next {end} {next_path}', f'saveg {out}/{name}.g']
    (out / (name + '.cfg')).write_text('\n'.join(cfg) + '\n')
emit('Front', 'AF01', 'AF05', out/'E0.cfg')
for i in range(6):
    extra = [f'x {i:x}', f'cell 8 {i:x}']
    emit(f'E{i}', 'AF05', 'AF0B', out/f'M{i}.cfg', extra)
    emit(f'M{i}', 'AF0B', 'AF05' if i < 5 else 'AF10',
         out/f'E{i+1}.cfg' if i < 5 else tail, extra)
