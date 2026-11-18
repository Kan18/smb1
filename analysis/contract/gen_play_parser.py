#!/usr/bin/env python3
"""Embed separately checked parser chunks, retaining their explicit open exits.

Usage: gen_play_parser.py CHUNKDIR SHARED.g LEANROOT
A saved object tuple and membership in the parser entry chain remain hypotheses.
"""
import json
import sys
from pathlib import Path
chunks, bounds, root = map(Path, sys.argv[1:])
manifest = json.loads((chunks / 'manifest.json').read_text())
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
text = f'''import Smb.Abs.Config

/-! Parser chunk data. Flag-creation and other non-normal exits remain open. -/
namespace Smb.Abs.PlayParser

def boundsText : String := {q(btext)}
def G : Global := Id.run do
  let mut g : Global := Array.replicate 0x800 VS.top
  for line in boundsText.splitOn "|" do
    match line.splitOn " " with
    | a :: vs => g := g.set! (Config.hx a) (Config.parseVals vs)
    | [] => pure ()
  return g

def closing : Config.C := Config.parse {q(config(chunks / 'Z-kept.cfg'))}

def accepted (prg : ByteArray) (c : Config.C) : Bool :=
  let T := c.tableWith G prg
  checkF (romOf prg) c.exitFn c.protFn G T &&
  c.entries.all (entryIn G T) &&
  (T.at 0x8178).all (fun b => closing.entries.any (Box.le G b)) &&
  [0x8082, 0x8085, 0x8087, 0x808A, 0x808C].all (fun pc => (T.at pc).isEmpty)

'''
imports, names, lemmas = [], [], []
for item in manifest:
    name = item['name']
    text += f'def {name} : Config.C := Config.parse {q(config(chunks / (name + ".cfg")))}\n\n'
    names.append(name)
    module = 'Smb.Routine.PlayParser' + name
    imports.append('import ' + module)
    lemma = 'checked' + name
    lemmas.append(lemma)
    (root / (module.replace('.', '/') + '.lean')).write_text(f'''import Smb.Game
import Smb.PlayParserData

namespace Smb.Routine.PlayParser
open Smb.Abs.PlayParser

theorem {lemma} : accepted Smb.prg {name} = true := by native_decide

end Smb.Routine.PlayParser
''')
text += 'def chunks : List Config.C := [' + ', '.join(names) + ']\n\n'
chain_cells = (Path(__file__).resolve().parent / '../engine_bounds/parser_chain.txt').read_text().splitlines()[0].split()[1:]
text += 'def chainCells : List UInt16 := [' + ', '.join('0x' + c for c in chain_cells) + ']\n\n'
text += '''def entryTuples : List Box := chunks.flatMap (·.entries)

def tupleProjection (e : Box) : Box :=
  { e with
    pc := 0x8178
    s := 0xFB
    a := .top
    x := .top
    y := .top
    p := .top
    cells := e.cells.filter (fun c => chainCells.contains c.1) }

def chainClosed (prg : ByteArray) (c : Config.C) : Bool :=
  ((c.tableWith G prg).at 0x8178).all (fun b =>
    (entryTuples.map tupleProjection).any (Box.le G b))

end Smb.Abs.PlayParser
'''

(root / 'Smb/PlayParserData.lean').write_text(text)
(root / 'Smb/Routine/PlayParser.lean').write_text('\n'.join(imports) + '''

/-! Every listed chunk passes its checker. This is not a whole-frame or level theorem. -/
namespace Smb.Routine.PlayParser
open Smb.Abs.PlayParser

theorem checked : chunks.all (accepted Smb.prg) = true := by
  simp only [chunks, List.all_cons, List.all_nil, ''' + ', '.join(lemmas) + ''', Bool.and_self]

end Smb.Routine.PlayParser
''')
