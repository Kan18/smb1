#!/usr/bin/env python3
"""Partition every parser entry into smaller, independently checked tables.

Usage: play_parser_chunks.py A.cfg Z.cfg OUTDIR [SIZE]
All original case lines are preserved, in order, exactly once. The Z-kept link
is diagnostic: a proof must restore the protected object tuple from saved RAM.
"""
import argparse
import json
import sys
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('parser_config', type=Path)
parser.add_argument('closing_config', type=Path)
parser.add_argument('out', type=Path)
parser.add_argument('size', type=int, nargs='?', default=32)
parser.add_argument('--stop-flag-creation', action='store_true',
    help='Leave explicit OPEN exits before flagpole/castle enemy creation; not a complete frame certificate')
args = parser.parse_args()
a, z, out, size = args.parser_config, args.closing_config, args.out, args.size
if size < 1:
    raise SystemExit('SIZE must be positive')
lines = a.read_text().splitlines()
cases = [l for l in lines if l.startswith('case ')]
if not cases:
    raise SystemExit('No parser cases found')
base = [l for l in lines if not l.startswith(('case ', 'saveg ', 'next ', 'maxboxes '))]
if args.stop_flag_creation:
    # These writes introduce IDs 0x30/0x31 outside the pre-flag enemy contract.
    # Reaching either boundary is an unresolved phase transition, NOT success.
    base += ['exit 99CB', 'exit 9866']
out.mkdir(parents=True, exist_ok=True)
(out / 'Z-kept.cfg').write_text('\n'.join(l for l in z.read_text().splitlines() if not l.startswith('case ')) + '\n')
manifest = []
for start in range(0, len(cases), size):
    name = f'A{start // size:03d}'
    part = cases[start:start + size]
    cfg = base + part + [f'next 8178 {out}/Z-kept.cfg', f'saveg {out}/{name}.g', 'maxboxes 40000']
    (out / (name + '.cfg')).write_text('\n'.join(cfg) + '\n')
    manifest.append({'name': name, 'first_case': start, 'count': len(part)})
assert sum(x['count'] for x in manifest) == len(cases)
(out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(f'{len(cases)} entries in {len(manifest)} chunks of at most {size}')
