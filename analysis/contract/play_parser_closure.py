#!/usr/bin/env python3
"""Generate parser tuple-closure diagnostics, separate from transition checks.

Usage: play_parser_closure.py CHUNKDIR ORIGINAL_A.cfg OUTDIR
Each nocheck run must return 3 with zero alarms and zero failed links. This
checks the tuple projection at ordinary returns, not phase exits or initial
reachability. The full transition checker is still required separately.
"""
import sys
from pathlib import Path
chunks, original, out = map(Path, sys.argv[1:])
cells = (Path(__file__).resolve().parent / '../engine_bounds/parser_chain.txt').read_text().splitlines()[0].split()[1:]
lines = original.read_text().splitlines()
constraints = [l for l in lines if l.startswith('cell ') and l.split()[1] in cells]
cases = [l for l in lines if l.startswith('case ')]
for line in cases:
    assert all(part.split('=')[0] in cells for part in line.split()[1:])
out.mkdir(parents=True, exist_ok=True)
(out/'Tuples.cfg').write_text('\n'.join(['entry 8178 FB', 'a top', 'x top', 'y top', 'p top'] + constraints + cases) + '\n')
for p in sorted(chunks.glob('A*.cfg')):
    base = [l for l in p.read_text().splitlines() if not l.startswith(('next ', 'saveg ', 'nocheck'))]
    (out/p.name).write_text('\n'.join(base + ['nocheck', f'next 8178 {out}/Tuples.cfg']) + '\n')
