#!/usr/bin/env python3
"""The head-hit region: `PlayerHeadCollision` from `$BCED` to its return at `$DCE7`, with Mario's horizontal bytes protected.

Usage: gen_head_hit.py OUT.cfg LEANFILE [collision]

With `collision`, the region is instead all of `PlayerBGCollision` from its entry (`$DC64`, called from `$B15A`) to the
points where something may move Mario: the side checks (`$DD5E`) and `ImpedePlayerMove` (`$DF4B`), and the early return
(`$DC97`), and a pipe entry (`$DEFA`), the side pipe (`$DDFC`), the flag grab (`$DE75`) or climbing (`$DE88`), which end the stretch of normal play; the module is then `Smb.Abs.Collision`.

Built from the normal-play cycle's player region (`Smb.PlayFrameData`'s `P`): its precision directives, and the
cycle's shared global bounds (`PlayParser.G`), which the cycle certificate shows hold at every instruction. What changes:

* the entry is `PlayerHeadCollision`'s, called from `HeadChk` (`$DCE4`), with the stack the call chain leaves
  (return addresses `$DCE7`, `$B15D`, `$AEF6`, `$8178` above the NMI's frame, as at the TAS's head hits);
* the block-buffer pointer `$06`/`$07` and row `$02` are as `BlockBufferColli_Head` leaves them;
* the buffer offsets are tracked from the entry values `NoOverflow` allows (`$0300` <= `$34`, `$0340` <= `$21`)
  instead of assumed, so the Plain checker needs no assumption;
* `VineFlagOffset` (`$0398`) starts at 0, as the shared bounds say, and the vine path's own writes (enemy 5's ID
  `$2F` and the offset reaching 1) are allowed, which widens two bounds of this region only;
* the protected cells are the horizontal bytes `HorizontalLimit` reads: speed, position, sub-pixel, screen edges,
  `Platform_X_Scroll`, last frame's on-screen X and the side-collision timer; and, for the foot check after it, `$EB`, `Y`, `$B5` and the player state. A head hit writes the vertical speed `$9F` (0, or `$FE` for a shattered brick), so that one is left free.

Nothing here is trusted: `Smb.Routine.HeadHit` has the checker accept the table computed from it.
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
out_cfg, out_lean = Path(sys.argv[1]), Path(sys.argv[2])
mode = sys.argv[3] if len(sys.argv) > 3 else 'head'
coll = mode != 'head'

# The normal-play cycle's player region (`PlayFrame`'s `P`) and its shared bounds (`PlayParser.G`).
data = (ROOT / 'lean/Smb/PlayFrameData.lean').read_text()
bounds = re.search(r'def boundsText : String := "([^"]*)"',
                   (ROOT / 'lean/Smb/PlayParserData.lean').read_text()).group(1).split('|')
player = None
for m in re.finditer(r'def (\w+) : Config\.C := Config\.parse ("(?:[^"\\]|\\.)*")', data):
    if m.group(1) == 'P':
        player = json.loads(m.group(2)).splitlines()
assert player is not None

drop = ('entry', 'exit', 'case', 'nocheck', 'saveg', 'next', 'nes', 'pin', 'assume', 'cell 1f')
lines = [l for l in player if l.strip() and not l.startswith(drop)]
glob = {}
for e in bounds:
    a, *vs = e.split()
    glob[a] = vs
for l in player:
    if l.startswith('global '):
        a, *vs = l.split()[1:]
        glob[a] = vs
glob.pop('0300', None)
glob.pop('0340', None)
glob['001b'] = glob['001b'] + ['2f']
glob['0398'] = ['00', '01']
lines = [l for l in lines if not l.startswith('global ')]
lines += [f'global {a} {" ".join(vs)}' for a, vs in sorted(glob.items())]
if mode in ('collision', 'bounds'):
    # The flags come out of the summaries before it as an unknown value with I set.
    lines = [l for l in lines if not l.startswith('p ')] + ['p ' + ' '.join(f'{v:02x}' for v in range(256) if v & 4)]
    if mode == 'collision':
        lines += ['entry DC64 F5'] + [f'exit {e}' for e in ['DF4B', 'B15D', 'DDFC', 'DE75', 'DE88']]
    else:
        # The same code on to PlayerHole, through the impede and the attribute update, for its bounds there.
        lines += ['entry DC64 F5'] + [f'exit {e}' for e in ['B179', 'DDFC', 'DE75', 'DE88']]
elif mode == 'pre':
    # The player region's own entry, with its cases, up to PlayerCtrlRoutine.
    # A frame after a pipe entry dispatches on $0E = 3 to VerticalPipeEntry ($B1E5), which ends normal play.
    lines += ['entry 8175 FB', 'exit B0E9', 'exit B1E5'] + [l for l in player if l.startswith('case ')]
elif mode == 'ctrl':
    # From PlayerCtrlRoutine's entry to PlayerBGCollision's: movement and scrolling, which move Mario, so nothing
    # horizontal is protected here; the region is for its bounds at $DC64.
    lines = [l for l in lines if not l.startswith('p ')] + ['p ' + ' '.join(f'{v:02x}' for v in range(256) if v & 4)]
    lines += ['entry B0E9 F7', 'exit DC64']
elif mode == 'post':
    # From PlayerHole to the player region's exits: its return into the engine, and a death in a pit.
    lines = [l for l in lines if not l.startswith('p ')] + ['p ' + ' '.join(f'{v:02x}' for v in range(256) if v & 4)]
    # Its exits: the return into the engine (`$AF01`) and a death in a pit (`$B1B8`), which ends normal play.
    lines += ['entry B179 F7', 'exit AF01', 'exit B1B8']
else:
    lines += ['entry BCED F3', 'exit DCE7']
stack = {'1f6': '5c', '1f7': 'b1', '1f8': 'f5', '1f9': 'ae', '1fa': '77', '1fb': '81',
         '1fc': '10 11 14 15', '1fd': '24 25 26 27 64 65 66 67 a4 a5 a6 a7 e4 e5 e6 e7', '1fe': '57', '1ff': '80'}
if mode == 'head':
    stack = {'1f4': 'e6', '1f5': 'dc', **stack}
elif mode in ('collision', 'bounds'):
    # $1F4/$1F5 are tracked rather than given, so the boxes record what the side check's `jsr` pushes there.
    lines += ['track 1f4', 'track 1f5']
elif mode in ('post', 'ctrl'):
    stack = {k: v for k, v in stack.items() if k >= '1f8'}
elif mode == 'pre':
    # The interrupt's frame under the game logic, which the routine's region asks for at $B0E9.
    stack = {k: v for k, v in stack.items() if k >= '1fc'}
else:
    stack = {}
lines += [f'cell {a} {v}' for a, v in stack.items()]
if not coll:
    lines += ['cell 7 5', 'cell 6 0-f d0-df', 'cell 2 0 10 20 30 40 50 60 70 80 90 a0 b0 c0']
lines += ['cell 398 0']
# The buffer offsets, tracked from what NoOverflow allows at the entry. The code after the routine never writes the
# VRAM buffers, so its region needs no bound on them: the collision code's records can leave $0300 past $34 there.
lines += ['track 300', 'track 340'] if mode == 'post' else ['track 300', 'cell 300 0-34', 'track 340', 'cell 340 0-21']
lines += [f'prot {p}' for p in ([] if mode in ('ctrl', 'bounds') else ['57', '86', '6D', '400', '71A 71D', '3A1', '755', '785', '705']) +
          ([] if coll else ['eb', 'ce', 'b5', '1d'])]
text = '\n'.join(lines) + '\n'
out_cfg.write_text(text)
EXTRA = '''
/-- Box `b` holds cell `a` at exactly `v`. -/
def cellIs (b : Box) (a : UInt16) (v : UInt8) : Bool :=
  b.cells.any fun c => c.1 == a && match c.2 with
    | .set [w] => w == v
    | _ => false

/-- At `ImpedePlayerMove`, the stack: `$B15C` on top for the foot check's `jmp`, or `$DE01` above it for the side
check's `jsr`. -/
def impedeStack (b : Box) : Bool :=
  cellIs b 0x1F6 0x5C && cellIs b 0x1F7 0xB1 &&
    (b.s == 0xF5 || (b.s == 0xF3 && cellIs b 0x1F4 0x01 && cellIs b 0x1F5 0xDE))

/-- The cells the attribute update writes (`$03C4`), and with them those `ImpedePlayerMove` writes. -/
def attrWritten (i : UInt16) : Bool := i == 0x3C4
def impAttrWritten (i : UInt16) : Bool :=
  i == 0x3C4 || i == 0x490 || i == 0x57 || i == 0x785 || i == 0x86 || i == 0x6D || i == 0

/-- An unconstrained value set. -/
def isTopV : VS → Bool
  | .top => true
  | _ => false

/-- The cells the impede may set to 0 and otherwise leaves: the X speed. -/
def zeroed (i : UInt16) : Bool := i == 0x57

/-- Box `e`'s registers are unconstrained, and each of its cells is covered by box `b` and either not written on the
way, or one that may only be zeroed (`zeroed`), with 0 allowed. -/
def coverAfter (g : Global) (b e : Box) (written : UInt16 → Bool) : Bool :=
  isTopV e.a && isTopV e.x && isTopV e.y && e.cells.all fun c =>
    cellCovered g b [] c && (!written c.1 || (zeroed c.1 && c.2.mem 0))

/-- `accepted`, and from the same table: no box at `PlayerHole` (`$B179`) or at the player region's return into the
engine (`$AF01`), every box at `ImpedePlayerMove` records one of the two stacks, and every box at the return
(`$B15D`, where the stack is back at `$F7`) or at `ImpedePlayerMove` covers the second region's entry once the attribute update (and the impede) have
written their cells. -/
def acceptedAll (prg : ByteArray) : Bool :=
  let T := conf.table prg
  check (romOf prg) conf.exitFn conf.protFn conf.globals T && conf.entries.all (entryIn conf.globals T) &&
    (T.at 0xB179).isEmpty && (T.at 0xAF01).isEmpty && (T.at 0xDF4B).all impedeStack &&
    (T.at 0xB15D).all (fun b => b.s == 0xF7 && PlayerPost.conf.entries.any fun e => coverAfter conf.globals b e attrWritten) &&
    (T.at 0xDF4B).all (fun b => PlayerPost.conf.entries.any fun e => coverAfter conf.globals b e impAttrWritten)
''' if mode == 'collision' else ''
out_lean.write_text(f'''import Smb.Abs.Config
{'import Smb.PlayerPostData' if mode == 'collision' else ''}

/-!
# {dict(head='The head-hit region', collision='The collision region', pre='The player region before the routine', post='The player region after the routine', ctrl='The routine up to the collision code', bounds='The collision code to PlayerHole, for its bounds')[mode]}

{dict(head='`PlayerHeadCollision` (`$BCED`), called from `HeadChk`, to its return at `$DCE7`', collision='`PlayerBGCollision` from its entry (`$DC64`) to the side checks, `ImpedePlayerMove`, its early return or a pipe entry', pre='The player region from its entry (`$8175`) to `PlayerCtrlRoutine` (`$B0E9`)', post='The player region from `PlayerHole` (`$B179`) to its exits', ctrl='`PlayerCtrlRoutine` from its entry (`$B0E9`) to `PlayerBGCollision` (`$DC64`)', bounds='`PlayerBGCollision` from its entry (`$DC64`) through `ImpedePlayerMove` and the attribute update to `PlayerHole` (`$B179`)')[mode]}, {'for its bounds there' if mode in ('ctrl', 'bounds') else "with Mario's horizontal bytes protected"}.
Generated by `analysis/contract/gen_head_hit.py` from the checked player region's bounds and directives. Nothing here is
trusted: `Smb.Routine.HeadHit` has the checker accept the table computed from it.
-/
namespace Smb.Abs.{dict(head='HeadHit', collision='Collision', pre='PlayerPre', post='PlayerPost', ctrl='PlayerCtrl', bounds='CollisionBounds')[mode]}

def text : String := {json.dumps(text)}

def conf : Config.C := Config.parse text

/-- The Plain checker accepts the table, and the table contains every entry box. -/
def accepted (prg : ByteArray) : Bool :=
  let T := conf.table prg
  check (romOf prg) conf.exitFn conf.protFn conf.globals T && conf.entries.all (entryIn conf.globals T)
{EXTRA}
end Smb.Abs.{dict(head='HeadHit', collision='Collision', pre='PlayerPre', post='PlayerPost', ctrl='PlayerCtrl', bounds='CollisionBounds')[mode]}
''')
print(f'{len(lines)} lines')
