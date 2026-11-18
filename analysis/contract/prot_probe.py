#!/usr/bin/env python3
"""Write the normal-play cycle's region configs, as Lean checks them, with extra protected cells, for smbabs.

usage: prot_probe.py OUTDIR CELL...          (cells in hex, e.g. 705 755 785)
       prot_probe.py --lean CELL...          add the same `prot` lines to the Lean data modules themselves

Takes each region's config text from the Lean data modules (`PlayFrameData`, `PlayEnemyData`, `PlayParserData`),
adds the shared bounds (`PlayParser.boundsText`) as `global` lines, drops `next` and `saveg`, and adds `prot CELL`
for each cell, except where the region is known to write it: `$0755` in the tail (`T`, `RenderPlayerSub`) and
`$0785` in `H` (the timers). The player region `P` is left out. Then, from the repository root:

    for f in OUTDIR/*.cfg; do lean/.lake/build/bin/smbabs "Super Mario Bros. (World).nes" $f | grep -E '^check|alarm sites'; done

A protected cell that a region writes shows up as an alarm at its writer. With `--lean` the configs' strings in
the three data modules get the `prot` lines in place, for re-checking the cycle in Lean (`lake build
Smb.Routine.PlayCycle`); `PlayKeep.restConfigs` then protects them, which `PlayKeepList.rest_run_list` uses.
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
lean = sys.argv[1] == '--lean'
out = None if lean else Path(sys.argv[1])
cells = sys.argv[2:]
skip = {'T': {'755'}, 'H': {'785'}}
if out:
    out.mkdir(parents=True, exist_ok=True)
bounds = re.search(r'def boundsText : String := "([^"]*)"',
                   (ROOT / 'lean/Smb/PlayParserData.lean').read_text()).group(1).split('|')
for module in ['PlayFrameData', 'PlayEnemyData', 'PlayParserData']:
    path = ROOT / f'lean/Smb/{module}.lean'
    data = path.read_text()
    if lean:
        def add(m):
            name, text = m.group(1), json.loads(m.group(2))
            if name in ('P', 'tail'):
                return m.group(0)
            extra = [f'prot {c}' for c in cells if c not in skip.get(name, set())]
            return f'def {name} : Config.C := Config.parse {json.dumps(text.rstrip(chr(10)) + chr(10) + chr(10).join(extra))}'
        path.write_text(re.sub(r'def (\w+) : Config\.C := Config\.parse ("(?:[^"\\]|\\.)*")', add, data))
        continue
    for m in re.finditer(r'def (\w+) : Config\.C := Config\.parse ("(?:[^"\\]|\\.)*")', data):
        name = m.group(1)
        if name in ('P', 'tail'):
            continue
        lines = [l for l in json.loads(m.group(2)).splitlines() if l.strip() and not l.startswith(('next ', 'saveg '))]
        given = {int(l.split()[1], 16) for l in lines if l.startswith(('global ', 'assume '))}
        glob = ['global ' + e for e in bounds if int(e.split()[0], 16) not in given]
        extra = [f'prot {c}' for c in cells if c not in skip.get(name, set())]
        (out / f'{name}.cfg').write_text('\n'.join(lines + glob + extra) + '\n')
