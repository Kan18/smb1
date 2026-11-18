#!/usr/bin/env python3
"""Write `lean/Smb/Routine/PlayWriters<region>.lean`, one per region of the normal-play cycle: `writersOk` on that
region's config, by `native_decide`. `PlayWritersAll` imports them all. Rerun after adding or renaming a region.

usage: gen_play_writers.py
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2] / 'lean/Smb/Routine'
DATA = {'PlayFrame': 'Smb.PlayFrameData', 'PlayEnemy': 'Smb.PlayEnemyData', 'PlayParser': 'Smb.PlayParserData'}
names = [('PlayFrame', 'H'), ('PlayFrame', 'P'), ('PlayEnemy', 'Front')]
for i in range(6):
    names += [('PlayEnemy', f'E{i}'), ('PlayEnemy', f'M{i}')]
names += [('PlayFrame', 'T'), ('PlayFrame', 'Z')] + [('PlayParser', 'A%03d' % i) for i in range(42)]
for ns, n in names:
    (ROOT / f'PlayWriters{n}.lean').write_text(f"""import Smb.Routine.PlayWritersDefs
import {DATA[ns]}

namespace Smb.Routine.PlayWriters

theorem ok{n} : writersOk Smb.Abs.{ns}.{n} = true := by native_decide

end Smb.Routine.PlayWriters
""")
print(len(names), 'modules')
