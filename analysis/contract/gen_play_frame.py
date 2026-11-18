#!/usr/bin/env python3
"""Embed surrounding play regions with the parser/enemy common globals.

Usage: gen_play_frame.py CONFIGDIR LEANROOT
These are local certificates. Entry reachability, tuple membership, exceptional
exits, timing, and whole-frame composition remain separate obligations.
"""
import json
import sys
from pathlib import Path
src, root = map(Path, sys.argv[1:])
skip = {'global', 'assume', 'saveg', 'max', 'maxboxes', 'next', 'dump', 'dumpc',
        'watch', 'promote', 'gwiden', 'nocheck', 'nogrow'}
def config(path):
    lines = [line.strip() for line in path.read_text().splitlines()
             if line.split() and line.split()[0] not in skip]
    return '\n'.join(lines + ['assume 300 00-34', 'assume 340 00-21',
                              'nogrow', 'max 10000000', 'promote FFFFFF'])
text = '''import Smb.PlayEnemyData

/-! Common play-region data, still conditional on entry and saved tuples. -/
namespace Smb.Abs.PlayFrame
abbrev G := PlayParser.G

'''
for n in ['H', 'P', 'T', 'Z']:
    text += f'def {n} : Config.C := Config.parse {json.dumps(config(src / (n+".cfg")))}\n\n'
text += '''def emptyPCs : List UInt16 := [0x8082, 0x8085, 0x8087, 0x808A, 0x808C]
def acceptedH (prg : ByteArray) : Bool :=
  H.linkedE G prg [(0x8178, Z.entries), (0x8175, P.entries)] emptyPCs

def acceptedP (prg : ByteArray) : Bool :=
  P.linkedE G prg [(0xAF01, PlayEnemy.Front.entries)] emptyPCs

def acceptedZ (prg : ByteArray) : Bool :=
  -- Closing includes the idle loop and the next NMI preamble.
  Z.linked G prg [(0x808F, H.entries)]

def parserEntries : List Box := PlayParser.chunks.flatMap (·.entries)
def chainKeep (i : UInt16) : Bool := PlayParser.chainCells.contains i

def objectProjection (e : Box) : Box :=
  { e with
    pc := 0xAF67
    s := 0xF9
    a := .top
    x := .top
    y := .top
    p := .top
    cells := e.cells.filter (fun k => k.1 == 0x739 || k.1 == 0x73B) }

def acceptedT (prg : ByteArray) : Bool :=
  let table := T.tableWith G prg
  checkF (romOf prg) T.exitFn T.protFn G table &&
  T.entries.all (entryIn G table) &&
  (table.at 0xAF67).all (fun b => parserEntries.all (fun e =>
    Box.le G b { e with cells := e.cells.filter (fun c => !chainKeep c.1) })) &&
  (table.at 0xAF67).all (fun b => (Z.entries.map objectProjection).any (Box.le G b)) &&
  emptyPCs.all (fun pc => (table.at pc).isEmpty)

end Smb.Abs.PlayFrame
'''
(root/'Smb/PlayFrameData.lean').write_text(text)
for n in ['H', 'P', 'T', 'Z']:
    (root/f'Smb/Routine/PlayFrame{n}.lean').write_text(f'''import Smb.Game
import Smb.PlayFrameData

namespace Smb.Routine.PlayFrame

theorem accepted{n} : Smb.Abs.PlayFrame.accepted{n} Smb.prg = true := by native_decide

end Smb.Routine.PlayFrame
''')
(root/'Smb/Routine/PlayFrame.lean').write_text(''.join(f'import Smb.Routine.PlayFrame{n}\n' for n in ['H','P','T','Z']))
