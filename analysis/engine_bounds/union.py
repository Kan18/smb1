#!/usr/bin/env python3
"""Union sparse bounds: a cell omitted by any input is unconstrained."""
import sys
from pathlib import Path

def read(path):
    bounds, tracked = {}, set()
    for lineno, line in enumerate(Path(path).read_text().splitlines(), 1):
        w = line.split('#', 1)[0].split()
        if not w:
            continue
        if w[0] == 'track' and len(w) in (2, 3):
            lo, hi = int(w[1], 16), int(w[-1], 16)
            if not 0 <= lo <= hi < 2048:
                raise ValueError(f'{path}:{lineno}: invalid track range')
            tracked.update(range(lo, hi + 1))
        elif w[0] == 'global' and len(w) >= 3:
            a = int(w[1], 16)
            if not 0 <= a < 2048 or a in bounds:
                raise ValueError(f'{path}:{lineno}: invalid/duplicate address')
            if w[2:] == ['top']:
                bounds[a] = None
            else:
                vals = set()
                for part in w[2:]:
                    ends = [int(x, 16) for x in part.split('-')]
                    if len(ends) not in (1, 2) or not 0 <= ends[0] <= ends[-1] < 256:
                        raise ValueError(f'{path}:{lineno}: invalid byte range')
                    vals.update(range(ends[0], ends[-1] + 1))
                bounds[a] = vals
        else:
            raise ValueError(f'{path}:{lineno}: unexpected row')
    return bounds, tracked

def main():
    if len(sys.argv) < 3:
        raise ValueError('usage: union.py OUT SAVED...')
    inputs = [read(p) for p in sys.argv[2:]]
    tracked = set().union(*(t for _, t in inputs))
    rows = []
    for a in range(2048):
        sets = [b.get(a) for b, _ in inputs]
        if a not in tracked and all(s is not None for s in sets):
            vals = set().union(*sets)
            rows.append(f'global {a:x} ' + ' '.join(f'{v:02x}' for v in sorted(vals)))
    rows += [f'track {a:x}' for a in sorted(tracked)]
    Path(sys.argv[1]).write_text('\n'.join(rows) + '\n')

if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError) as e:
        sys.exit(str(e))
