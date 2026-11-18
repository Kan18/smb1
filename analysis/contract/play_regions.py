#!/usr/bin/env python3
"""Write one smbabs config per stretch of a frame of play on 1-1's surface, before the flagpole: enemies, scrolling and the parser all running. The player routine is a region here, unlike in the
launch, because its collision code can take any path. usage: play_regions.py OUTDIR [--speed]
Splits are local wherever they can be: a split that holds across a whole region multiplies its boxes, and most only matter at a few addresses."""
import os, sys
out = sys.argv[1]
speed = "--speed" in sys.argv[2:]
here = os.path.dirname(os.path.abspath(__file__))
DONE = 'D958 91BA 9277 B0D5 B1B8 B27A B8AA D948 DDFC DE75 DE86 DF01 FAEF 8031 82CB 82F2 8483 91E5 9260 927E DE15 82CE 82FD 845D 8475 874E 905D 90C8 91E0 9233 925A 9279 B218 D009 DE10'.split()
P = 'p 24 25 26 27 64 65 66 67 A4 A5 A6 A7 E4 E5 E6 E7'
STACK = ['cell 1fd 24 25 26 27 64 65 66 67 a4 a5 a6 a7 e4 e5 e6 e7', 'cell 1fe 57', 'cell 1ff 80']
MIRROR = ['cell 1fc 10 11 14 15']
RET = ['cell 1fa 77', 'cell 1fb 81']
# Mario's position and the screen's edges: only the player routine moves them
KEEP = ['prot 57', 'prot 86', 'prot 6D', 'prot 400', 'prot 71A 71D', 'prot 3A1']
# The parser's and the enemy list's state, carried through every region
OBJ = ['track 72c', 'cell 72c ' + ' '.join(f'{i:x}' for i in range(2, 0x8C, 2)), 'track 6a0', 'cell 6a0 0-1f', 'track 726', 'cell 726 0-f', 'track 71f', 'cell 71f 0-8', 'track 739', 'track 73b',
       'case 73b=0 739=0,3,5,7,9,b,d,f,11,13,15,17,19,1b,1d', 'case 73b=1 739=0,3,5,7,b,d,f,11,13,15,17,1b,1d']
COMMON = ['exit ' + d for d in DONE] + ['nes', P, 'track 0 F', 'track e0 ef', 'assume 300 00-34', 'assume 340 00-21', 'gwiden 8', 'cell e 8', 'prot e', 'prot 770', 'prot 772',
          'splita 8E04 8E18', 'splity 8E04 8E18', 'promote 10000', 'splita B76C B772', 'splita B79A B79D', 'splitc 73b'] + OBJ
# These steer control flow, so a write outside one is an alarm at its writer. The enemy types are 1-1's, and ID 1 because a bump can create one.
PINS = {0xF: '0 1', 0x10: '0 1', 0x11: '0 1', 0x12: '0 1', 0x13: '0 1', 0x14: '0 1', 0x1D: '0-3', 0x39: '0-3', 0x756: '0-2', 0x16: '0 1 6', 0x17: '0 1 6', 0x18: '0 1 6', 0x19: '0 1 6', 0x1A: '0 1 6', 0x1B: '0 1 6 2e',
        0x398: '0', 0x6CD: '0', 0x6CB: '0', 0x6D7: '0', 0x3EC: '0 1', 0x3ED: '0 1', 0xE9: '1', 0xEA: '9f'}
ROWS = ' '.join(f'{r:x}' for r in range(0, 0xD0, 0x10))
COLS = '0-f d0-df'
GLOB = {0xE: '8', 0xE7: '90', 0xE8: 'a6', 0xE9: '1', 0xEA: '9f', 0x734: '0-9', 0x71F: '0-7', 0x720: '20 24', 0x727: '1', 0x728: '0', 0x729: '0', 0x72A: '1 2 3 4 c', 0x72B: '0 1', 0x72D: '0', 0x72E: '0 8',
        0x72F: '2 a c e 10 12 14 5c 5e 60', 0x730: 'ff', 0x731: 'ff', 0x732: '0-5 ff', 0x733: '0', 0x735: '0 b', 0x741: '0', 0x742: '2', 0x743: '0', 0x745: '0', 0x74E: '1', 0x753: '0', 0x77A: '0', 0x758: '0', 0x76A: '0',
        0x754: '0 1', 0x714: '0 4', 0x704: '0 1',
        0x770: '1', 0x772: '3', 0x778: '10 11 14 15', 0x779: '6 1e', 0x6CC: '0', 0x716: '0', 0x3EE: '0 1',
        # Where a bumped block sits in the block buffer: its row, and its column's low byte
        0x3E4: ROWS, 0x3E5: ROWS, 0x3E6: COLS, 0x3E7: COLS,
        **{a: '0' for a in range(0x46B, 0x471)},
        # A misc object's parent enemy, which the hammer code indexes by
        **{a: '0-5' for a in range(0x6AE, 0x6B7)},
        }
BLOCKS = open(os.path.join(here, '../engine_bounds/parser_blocks.txt')).read().strip() + ' 23 c4'
# The saved tile is restored to the block buffer at $BEF4, so it must use the
# same tile set. Letting it contain arbitrary scratch values breaks that closure.
GLOB.update({0x3E8: BLOCKS, 0x3E9: BLOCKS})
# What a probe past the block buffer reads. A probe's row wraps to `$D0` and up when Mario's above the screen or below it. The metatile buffer holds tiles, and what's after it is mostly constant.
BEYOND = {**{a: BLOCKS + ' 0-1f' for a in range(0x6A1, 0x6AE)}, 0x6AF: '0', 0x6B7: '0-8 23', **{a: '0' for a in range(0x6B8, 0x6D0) if a not in (0x6CB, 0x6CC, 0x6CD)}, 0x6C9: '0 ff'}
GLOB.update(BEYOND)
# A probe past the block buffer's last row reads whatever comes after it, and its store goes to the same place. That needs the exact address only when the column is in the buffer's second half and the
# tile isn't 0: every other case stays in the block buffer or stores nothing. Here's where the split is made, then where it's used.
PROBE = ['splita 9BF3 9BF5', 'splitcr 6 9BF3 9BF5', 'splitcr 6 E408 E41A', 'splitab E418 E41A d0 e0 f0', 'splitcg 6 E41A E41D 2 d0', 'splitcg 2 E41A E41D 2 d0', 'splitab E41D E41F 1']
def probe_uses(lo, hi):
    return [f'splitcb 2 {lo} {hi} d0', f'splitcb 3 {lo} {hi} 1', f'splitcg 6 {lo} {hi} 2 d0 6 d0 3 1', f'splitcg 2 {lo} {hi} 2 d0 6 d0 3 1']
PROBE += probe_uses('E41F', 'E431')
ENEMY = PROBE + probe_uses('DFC0', 'E1E0') + probe_uses('E388', 'E3AD') + probe_uses('E388', 'E3AD') + ['splitc 8', 'splitcr 3 8F11 8F60', 'splity 89EF 89F9', 'splity 8600 8622', 'splity C120 C2A0', 'splity 8F1C 8F3A', 'splita 8F11 8F1C', 'splity C886 C88F', 'track 1b']
# Mario's Y against each limit the collision code compares it with, and the sensor it goes with: together they keep every probe inside the block buffer
PLAYER = ['splity E3E8 E431', 'splitab DC93 DC96 cf', 'splitab DCBC DCBF 10 20', 'splitab DCFA DCFC cf', 'splitab DD6B DD71 20 e4', 'splitab DD8A DD90 8 d0', 'splity BDF6 BE01', 'track ce', 'track 714', 'track 754', 'track 704', 'splitcr 714 DC98 DCC4', 'splitcr 754 DC98 DCC4', 'splitcr 704 DC98 DCC4',
          'splitcr 3 8F11 8F60', 'splity 8F1C 8F3A', 'splita 8F11 8F1C', 'fast'] + ['track ' + c for c in 'bf 6bc 78 77 76 b5 73 6d 3eb 3ea 723 9f 75e 71a 398 748 81'.split()]
# Keep the head sensor paired with the Y lower bound, including across the
# helper that overwrites Y while computing the block-buffer pointer.
PLAYER += ['splity DCAB DCC4', 'splitcr 4 9BE1 9BF5',
           'splitcb ce DC91 DCC4 10 20 cf', 'splitcb ce E3E8 E431 10 20 cf', 'splitcb ce 9BE1 9BF5 10 20 cf']
# The two side-probe iterations must not merge. Otherwise $00 can regain 2 on
# the back edge and $EB walks beyond the 21-entry sensor tables.
PLAYER += ['splitcr 0 DD5E DD9B', 'splitcr 0 E3E8 E431', 'splitcr 0 9BE1 9BF5', 'splitcr 0 DF9A DFBE']
PARSER = ['splita 92DE 92E5', 'splitcr 1 88D0 8943', 'splity 9445 9455', 'splity 92B0 92C0', 'splity 9508 9570', 'splity 9589 9664', 'splity 9BBB 9BCA', 'splity 9BB0 9BBA', 'splitvr 9508 9CFF', 'splitvr 8E04 8E18',
          'track 72d 72f', 'splitv 72d 8', 'splitc 8', 'track 730 732', 'track 729 72b', 'track 734 735', 'track 73', 'track 71', 'track 70', 'track 6f', 'track 6e', 'track 725', 'track 721', 'track 14']
# Optional stronger phase contract. Unlike the baseline certificate, this
# excludes climbing and carries the speed limit only at region boundaries;
# friction may temporarily exceed it before the ROM's clamp.
if speed:
    PINS[0x1D] = '0-2'
    PINS.update({0x450: '0 d8 e8 f0', 0x456: '0 0c 10 18 28',
                 0x701: '0 1', 0x702: '0 30 98 a0 c8 d0 e4'})
    COMMON += ['cell 57 0-28 d8-ff']
    KEEP += ['prot 450', 'prot 456', 'prot 701 702']
    # Keep the tile's high-bit class tied to its original value at the climb
    # comparison. Otherwise non-climbable tiles can take the climbing branch.
    PLAYER += ['splity DFB0 DFB8', 'splitab DF9D DFA0 24 26 6d 8a c6',
               'splitab DDA4 DDA6 24 26 6d 8a c6',
               'track 57', 'track 701 702',
               'splitab B5E8 B617 29 80 d8', 'splitcb 57 B5E8 B617 29 80 d8']
REGIONS = {
  'H': ('808F', 'FC', ['exit 8175', 'exit 8178'], ['frame', 'widen F2D0 FFF9', 'track 776', 'cell 776 0 1 80 81'] + STACK),
  'P': ('8175', 'FB', ['exit AF01'], PLAYER + STACK + MIRROR),
  'E': ('AF01', 'F9', ['exit AF10'], ENEMY + STACK + RET + MIRROR),
  'T': ('AF10', 'F9', ['exit AF67', 'exit B79A'], ['splitcr 3 8F11 8F60', 'splitcr 0 89E1 8A40', 'splita B9CF B9D6', 'splity 89EF 89F9', 'splity 8600 8622', 'track 3ec 3ed', 'cell 3ec 0 1', 'cell 3ed 0 1', 'splita BEE0 BEE2', 'splitcr 8 8A61 8B07', 'splitcr 8 863F 8642'] + STACK + RET + MIRROR),
  'A': ('AF67', 'F9', ['exit 8178'], PARSER + STACK + RET + MIRROR),
  'Z': ('8178', 'FB', ['exit 808F'], ['frame'] + STACK + MIRROR),
}
NEXT = {'8175': 'P', 'AF01': 'E', 'AF10': 'T', 'AF67': 'A', '8178': 'Z', '808F': 'H'}
CHAIN = open(os.path.join(here, '../engine_bounds/parser_chain.txt')).read().splitlines()
CELLS = CHAIN[0].split()[1:]
TRACKED = [c for c in CELLS if not c.startswith('e')]
def chain_cases():
    return ['case ' + ' '.join(f'{c}={row[2 * i:2 * i + 2]}' for i, c in enumerate(CELLS) if row[2 * i:2 * i + 2] != '..') for row in CHAIN[1:]]
def chain_bounds():
    rows = []
    for i, c in enumerate(CELLS):
        vals = {row[2 * i:2 * i + 2] for row in CHAIN[1:]}
        if '..' not in vals:
            rows.append(f'global {c} ' + ' '.join(sorted(vals)))
    return rows
NCELLS = {int(c, 16) for c in CELLS}
glob = [f'global {a:x} {v}' for a, v in {**GLOB, **PINS}.items() if a not in NCELLS] + [f'pin {a:x}' for a in PINS] + [f'pin {a:x}' for a in (0x3E4, 0x3E5, 0x3E8, 0x3E9, 0x3E6, 0x3E7)] + [f'pin {a:x}' for a in range(0x500, 0x6A0)] + [f'global {c:x} {BLOCKS}' for c in range(0x500, 0x6A0)]
for name, (pc, s, ex, hints) in REGIONS.items():
    nx = [f'next {e.split()[1]} {out}/{NEXT[e.split()[1]]}.cfg' for e in ex if e.split()[1] in NEXT]
    # $0705 (the speed's fraction), $0755 (last frame's on-screen X) and $0785 (the side-collision timer): only the
    # player routine writes them, apart from the tail's copy into $0755 and the timers' countdown of $0785 in H.
    more = [c for c in ('705', '755', '785') if not (name == 'T' and c == '755') and not (name == 'H' and c == '785')]
    keep = [] if name == 'P' else KEEP + ['prot ' + c for c in more]
    common = COMMON
    extra = chain_bounds() + ['prot ' + c for c in CELLS]
    if name == 'A':
        drop = {'track 739', 'track 73b', 'splitc 73b'}
        common = [l for l in COMMON if not l.startswith('case ') and l not in drop]
        extra = chain_cases() + ['track ' + c for c in TRACKED] + ['splitc ' + ' '.join(CELLS), 'prot 739', 'prot 73b']
    lines = [f'entry {pc} {s}'] + ex + common + keep + hints + glob + extra + nx + [f'saveg {out}/{name}.g', 'max 3000000', 'maxboxes F4240']
    open(f'{out}/{name}.cfg', 'w').write('\n'.join(lines) + '\n')
