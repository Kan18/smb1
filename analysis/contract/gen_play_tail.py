#!/usr/bin/env python3
"""Embed a tail certificate whose parser tuple is supplied separately.

Usage: gen_play_tail.py TAIL.cfg SHARED.g PARSER.cfg LEANROOT
The native check verifies every parser entry after dropping protected cells.
It does not establish that the saved parser tuple belongs to that entry set.
"""
import json
import sys
from pathlib import Path

tail, bounds, parser, root = map(Path, sys.argv[1:])
skip = {'global', 'assume', 'saveg', 'max', 'maxboxes', 'next', 'dump', 'dumpc',
        'watch', 'promote', 'gwiden', 'nocheck', 'nogrow'}

def config(path):
    lines = [line.strip() for line in path.read_text().splitlines()
             if line.split() and line.split()[0] not in skip]
    return '\n'.join(lines + ['assume 300 00-34', 'assume 340 00-21',
                              'nogrow', 'max 10000000', 'promote FFFFFF'])

btext = '|'.join(' '.join(w[1:]) for line in bounds.read_text().splitlines()
                 if (w := line.split()) and w[0] == 'global' and w[2] != 'top')
q = json.dumps
(root / 'Smb/PlayTailData.lean').write_text(f'''import Smb.Abs.Config

/-! General tail candidate. Its saved parser tuple is a separate hypothesis. -/
namespace Smb.Abs.PlayTail

def boundsText : String := {q(btext)}
def G : Global := Id.run do
  let mut g : Global := Array.replicate 0x800 VS.top
  for line in boundsText.splitOn "|" do
    match line.splitOn " " with
    | a :: vs => g := g.set! (Config.hx a) (Config.parseVals vs)
    | [] => pure ()
  return g

def tail : Config.C := Config.parse {q(config(tail))}
def parser : Config.C := Config.parse {q(config(parser))}

def accepted (prg : ByteArray) : Bool :=
  let T := tail.tableWith G prg
  checkF (romOf prg) tail.exitFn tail.protFn G T &&
  tail.entries.all (entryIn G T) &&
  (T.at 0xAF67).all (fun b => parser.entries.all (fun e =>
    Box.le G b {{ e with cells := e.cells.filter (fun c => !tail.protFn c.1) }})) &&
  [0x8082, 0x8085, 0x8087, 0x808A, 0x808C].all (fun pc => (T.at pc).isEmpty)

end Smb.Abs.PlayTail
''')
(root / 'Smb/Routine/PlayTail.lean').write_text('''import Smb.Game
import Smb.PlayTailData

/-! A tail-region check, conditional on a separately carried parser tuple. -/
namespace Smb.Routine.PlayTail

theorem accepted : Smb.Abs.PlayTail.accepted Smb.prg = true := by native_decide

end Smb.Routine.PlayTail
''')
