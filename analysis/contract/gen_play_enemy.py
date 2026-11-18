#!/usr/bin/env python3
"""Embed all enemy-loop segments, sharing PlayParserData's common global bounds.

Usage: gen_play_enemy.py SEGMENTDIR TAIL.cfg LEANROOT
Requires gen_play_parser.py to have used the same shared bounds. The table and
all segment links are recomputed and checked by Lean, not trusted from logs.
"""
import json
import sys
from pathlib import Path
out, tail, root = map(Path, sys.argv[1:])
skip = {'global', 'assume', 'saveg', 'max', 'maxboxes', 'next', 'dump', 'dumpc',
        'watch', 'promote', 'gwiden', 'nocheck', 'nogrow'}
def config(path):
    lines = [line.strip() for line in path.read_text().splitlines()
             if line.split() and line.split()[0] not in skip]
    return '\n'.join(lines + ['assume 300 00-34', 'assume 340 00-21',
                              'nogrow', 'max 10000000', 'promote FFFFFF'])
names = ['Front'] + [s for i in range(6) for s in (f'E{i}', f'M{i}')]
text = '''import Smb.PlayParserData

/-! Six enemy iterations, without combining their abstract tables. -/
namespace Smb.Abs.PlayEnemy
abbrev G := PlayParser.G

'''
for name in names + ['tail']:
    p = tail if name == 'tail' else out / (name + '.cfg')
    text += f'def {name} : Config.C := Config.parse {json.dumps(config(p))}\n\n'
links = [('Front', 'AF05', 'E0')]
for i in range(6):
    links += [(f'E{i}', 'AF0B', f'M{i}'),
              (f'M{i}', 'AF05' if i < 5 else 'AF10', f'E{i+1}' if i < 5 else 'tail')]
imports = []
for name, pc, target in links:
    text += f'''def accepted{name} (prg : ByteArray) : Bool :=
  {name}.linkedE G prg [(0x{pc}, {target}.entries)]
    [0x8082, 0x8085, 0x8087, 0x808A, 0x808C]

'''
    module = 'Smb.Routine.PlayEnemy' + name
    imports.append('import ' + module)
    (root / (module.replace('.', '/') + '.lean')).write_text(f'''import Smb.Game
import Smb.PlayEnemyData

namespace Smb.Routine.PlayEnemy
open Smb.Abs.PlayEnemy

theorem checked{name} : accepted{name} Smb.prg = true := by native_decide

end Smb.Routine.PlayEnemy
''')
text += 'end Smb.Abs.PlayEnemy\n'
(root / 'Smb/PlayEnemyData.lean').write_text(text)
(root / 'Smb/Routine/PlayEnemy.lean').write_text('\n'.join(imports) + '\n')
