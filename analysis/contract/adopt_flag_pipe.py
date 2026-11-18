#!/usr/bin/env python3
"""Widen the normal-play cycle to the flag-loaded frames and the pipe-entry frame, in the Lean data modules in place.

usage: adopt_flag_pipe.py          (idempotent: run it again after regenerating the data modules)

- Shared bounds (`PlayParser.boundsText`): `$0E` in {3, 8}; the enemy slots' IDs also `$30` (flagpole flag) and
  `$31` (star flag); slot 5's flag (`$14`) unbounded, since `FlagpoleObject` increments it unguarded;
  `StarFlagTaskControl` (`$0746`) 0, true before the grab; `$0704`, `$070B`, `$070E` 0 (no swimming, size change or
  jumpspring in normal play); `WarpZoneControl` (`$06D6`) 0, as in 1-1, so the pipe entry's warp-zone branch
  (`$DF0C`) isn't taken.
- Every config: entry boxes allow `$0E` = 3; `exit DF01` (where the pipe entry sets `$0E` = 3) is dropped.
- The player region `P`: no longer protects `$0E`, and stops at `VerticalPipeEntry` (`$B1E5`), where the next
  frame's dispatch on `$0E` = 3 goes.
- The parser chunks: the flag-creation stops (`exit 99CB`, `exit 9866`) are dropped.
- The enemy segments `E0`-`E4`: track and split their own slot's ID, so `RunEnemyObjectsCore`'s small-ID branch
  doesn't reach `EnemyMovementSubs` with `$30`/`$31`.
- The cycle's stops (`PlayCycleMeta.openExits`): without `$DF01`, `$99CB`, `$9866`; with `$B1E5`.

The generated regions are checked in Lean.
"""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CFG = re.compile(r'def (\w+) : Config\.C := Config\.parse ("(?:[^"\\]|\\.)*")')


def edit(name, lines):
    out = []
    for l in lines:
        if l == 'cell e 8':
            l = 'cell e 3 8'
        if l == 'exit DF01' or l in ('exit 99CB', 'exit 9866'):
            continue
        if name == 'P' and l == 'prot e':
            continue
        out.append(l)
    extra = ['exit B1E5'] if name == 'P' else []
    if re.fullmatch(r'E[0-4]', name):
        cell = '%x' % (0x16 + int(name[1]))
        extra += ['track ' + cell, 'splitc ' + cell]
    return out + [l for l in extra if l not in out]


for module in ['PlayFrameData', 'PlayEnemyData', 'PlayParserData']:
    path = ROOT / f'lean/Smb/{module}.lean'
    data = path.read_text()
    data = CFG.sub(lambda m: f'def {m.group(1)} : Config.C := Config.parse '
                   f'{json.dumps(chr(10).join(edit(m.group(1), json.loads(m.group(2)).splitlines())) + chr(10))}', data)
    if module == 'PlayParserData':
        def bounds(m):
            entries = m.group(1).split('|')
            out = []
            for e in entries:
                a, *vs = e.split()
                ai = int(a, 16)
                if ai == 0x0E:
                    vs = ['03', '08']
                if 0x16 <= ai <= 0x1B:
                    vs = sorted(set(vs) | {'30', '31'})
                if ai == 0x14:
                    continue
                if ai in (0x704, 0x70B, 0x70E, 0x746, 0x6D6):
                    continue
                out.append(' '.join([a] + vs))
            out += ['06d6 00', '0704 00', '070b 00', '070e 00', '0746 00']
            out.sort(key=lambda e: int(e.split()[0], 16))
            return 'def boundsText : String := "' + '|'.join(out) + '"'
        data = re.sub(r'def boundsText : String := "([^"]*)"', bounds, data)
    path.write_text(data)

meta = ROOT / 'lean/Smb/Routine/PlayCycleMeta.lean'
text = meta.read_text()
text = re.sub(r', 0xDF01', '', text, count=1)
text = text.replace(', 0x99CB, 0x9866]', ', 0xB1E5]')
assert '0xB1E5' in text
meta.write_text(text)
