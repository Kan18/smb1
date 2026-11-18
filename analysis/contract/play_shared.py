#!/usr/bin/env python3
"""Generate the common normal-play candidate, not an established run invariant.

Usage: play_shared.py SPEED_PLAYER.g SPEED_TAIL.g OUTDIR [EXTRA.g ...]
First generate --speed configs with play_regions.py and obtain their converged
player/tail globals with smbabs. This merges those bounds and adds the explicit
parser-row, level/world and pause hypotheses documented in the continuation log.
The generated configs use nogrow: every further missing bound is an alarm.
"""
import subprocess
import sys
from pathlib import Path

pfile, tfile, out = map(Path, sys.argv[1:4])
extra = list(map(Path, sys.argv[4:]))
here = Path(__file__).resolve().parent

def read(path):
    vals = {}
    for line in path.read_text().splitlines():
        w = line.split()
        if not w or w[0] != 'global':
            continue
        a = int(w[1], 16)
        if a in vals:
            raise ValueError(f'duplicate bound {a:x} in {path}')
        if w[2:] == ['top']:
            vals[a] = None
        else:
            vs = set()
            for token in w[2:]:
                lo, _, hi = token.partition('-')
                vs.update(range(int(lo, 16), int(hi or lo, 16) + 1))
            vals[a] = vs
    if set(vals) != set(range(0x800)):
        raise ValueError(f'{path} must contain all 2048 global cells')
    return vals

sources = [read(f) for f in [pfile, tfile] + extra]
values = {}
for a in range(0x800):
    v = None if any(s[a] is None for s in sources) else set().union(*(s[a] for s in sources))
    values[a] = 'top' if v is None else ' '.join(f'{x:02x}' for x in sorted(v))
blocks = (here / '../engine_bounds/parser_blocks.txt').read_text().strip() + ' 23 c4 0-f'
for a in range(0x6A1, 0x6AE):
    values[a] = blocks
for a in (0x75C, 0x75F, 0x760):
    values[a] = '0'
values[0x776] = '0 1 80 81'
# Extra calibration bounds must respect the explicit phase hypotheses.
# The original P/T bounds can be broader: these restrictions are intentional.
for f, source in zip(extra, sources[2:]):
    for a in [*range(0x6A1, 0x6AE), 0x75C, 0x75F, 0x760, 0x776]:
        allowed = set()
        for token in values[a].split():
            lo, _, hi = token.partition('-')
            allowed.update(range(int(lo, 16), int(hi or lo, 16) + 1))
        if source[a] is None or not source[a] <= allowed:
            raise ValueError(f'{f}: calibration violates phase hypothesis at {a:04x}')
g = [f'global {a:04x} {v}' for a, v in sorted(values.items())]
out.mkdir(parents=True, exist_ok=True)
subprocess.run([sys.executable, str(here / 'play_regions.py'), str(out), '--speed'], check=True)
(out / 'G.g').write_text('\n'.join(g) + '\n')
for name in ('H', 'P', 'E', 'T', 'A', 'Z'):
    path = out / f'{name}.cfg'
    lines = [l for l in path.read_text().splitlines()
             if not l.startswith(('global ', 'saveg ', 'nocheck'))]
    if name == 'E':
        # Keep the two side-probe iterations distinct across their helpers.
        lines += ['splitcr eb E10A E123', 'splitcr eb E388 E431',
                  'splitcr eb 9BE1 9BF5', 'splitcr eb E1B5 E1C7',
                  'splity E10A E123']
    lines += [l for l in g if int(l.split()[1], 16) not in (0x300, 0x340)]
    lines += ['nogrow', 'pin 776', 'pin 75c', 'pin 75f', 'pin 760', f'saveg {out}/{name}.g']
    path.write_text('\n'.join(lines) + '\n')

# Diagnostic links only. The actual proof must restore these cases from saved
# RAM, as PlayTailFacts.parser_entry does; these are not full parser entries.
a = (out / 'A.cfg').read_text()
(out / 'A-without-tuples.cfg').write_text('\n'.join(l for l in a.splitlines() if not l.startswith('case ')) + '\n')
t = (out / 'T.cfg').read_text().replace(f'next AF67 {out}/A.cfg', f'next AF67 {out}/A-without-tuples.cfg')
(out / 'T-kept.cfg').write_text(t)
