#!/usr/bin/env python3
"""Write one smbabs config per region of a gameplay frame, from one contract. usage: regions.py BOUNDS.g OUTDIR
Each region ends where the next begins, and the entry boxes state what must hold there. `Smb.Routine` theorems check that each region's boxes
at its exit lie in the next region's entry boxes."""
import os, sys
bounds, out = sys.argv[1:3]
P = 'p 24 25 26 27 64 65 66 67 A4 A5 A6 A7 E4 E5 E6 E7'
PS = 'cell 1fd 24 25 26 27 64 65 66 67 a4 a5 a6 a7 e4 e5 e6 e7'
MIRROR = 'cell 1fc 10 11 14 15'
STACK = [PS, 'cell 1fe 57', 'cell 1ff 80']
RET = ['cell 1fa 77', 'cell 1fb 81']
# the parser's and the enemy list's state, carried through every region
OBJ = ['track 72c', 'cell 72c ' + ' '.join(f'{i:x}' for i in range(2, 0x8C, 2)),
       'track 6a0', 'cell 6a0 0-1f', 'track 726', 'cell 726 0-f', 'track 71f', 'cell 71f 0-8',
       'track 739', 'track 73b',
       'case 73b=0 739=0,3,5,7,9,b,d,f,11,13,15,17,19,1b,1d', 'case 73b=1 739=0,3,5,7,b,d,f,11,13,15,17,1b,1d']
# every store to $0E (the player's routine), OperMode and OperMode_Task: normal control ends there
DONE = '91BA 9277 B0D5 B1B8 B27A B8AA D948 DDFC DE75 DE86 DF01 FAEF 8031 82CB 82F2 8483 91E5 9260 927E DE15 82CE 82FD 845D 8475 874E 905D 90C8 91E0 9233 925A 9279 B218 D009 DE10'.split()
EXITS = ['exit ' + d for d in DONE]
COMMON = EXITS + ['nes', P, 'track 0 F', 'track e0 ef', 'assume 300 00-34', 'assume 340 00-21', 'gwiden 8', 'cell e 8', 'global e 8', 'prot e', 'prot 770', 'prot 772',
          'splita 8E04 8E18', 'splity 8E04 8E18', 'promote 10000', 'splitc 73b', 'splita B76C B772', 'splita B79A B79D']
PARSER = ['splita 92DE 92E5', 'splitcr 1 88D0 8943', 'splity 9445 9455', 'splity 92B0 92C0', 'splity 9508 9570', 'splity 9589 9664', 'splity 9BBB 9BCA', 'splity 9BB0 9BBA', 'splitvr 9508 9CFF', 'splitvr 8E04 8E18',
          'track 72d 72f', 'splitv 72d 8', 'splitc 8', 'track 730 732', 'track 729 72b', 'track 734 735',
          'track 73', 'track 71', 'track 70', 'track 6f', 'track 6e', 'track 725', 'track 721', 'track 14']
ENEMY = ['splitc 0 3 8 73b', 'splity 89EF 89F9', 'splity 8600 8622', 'splity C120 C2A0', 'splity 8F1C 8F3A', 'splita 8F11 8F1C', 'track 16 1B', 'splity C886 C88F']
PLAYER = ['splity BDF6 BE01', 'track ce', 'splita DC91 DC96', 'splita DCF8 DCFD', 'track 714', 'track 754', 'track 704', 'splitcr 714 DC98 DCC4', 'splitcr 754 DC98 DCC4', 'splitcr 704 DC98 DCC4', 'splita DCBC DCBF', 'splitc 0 3', 'splity 8F1C 8F3A', 'splita 8F11 8F1C', 'fast'] + ['track ' + c for c in 'bf 6bc 78 77 76 b5 73 6d 3eb 3ea 723 9f 75e 71a 398 748 81'.split()]
# Mario's X position and the screen edges: only the player routines may write them
KEEP = ['prot 86', 'prot 6D', 'prot 71A 71D']
# The goal covers every input, and the title screen's Select starts a two-player game, which the movies' seeds don't show
ALSO = {0x77A: '0 1', 0x753: '0 1', 0xE9: '1 33', 0xEA: '9f a1'}
# These steer control flow, so their bounds are stated, not found: a write outside one is an alarm at its writer
PINS = {0xF: '0 1', 0x10: '0 1', 0x11: '0 1', 0x12: '0 1', 0x13: '0 1', 0x1D: '0-3', 0x39: '0-3', 0x756: '0-2', 0x16: '0 1 6 31', 0x17: '0 1 6 31', 0x18: '0 1 6 31', 0x19: '0 1 6 31', 0x1A: '0 1 6 31', 0x1B: '0 1 6 2e 30 31', 0x758: '0', 0x398: '0', 0x6CD: '0'}
# What the block buffers can hold starts from what the parser writes on its chain (close_chain.sh records it), and the other writers grow it.
# BLOCKS_EMPTY starts from nothing, for close_chain.sh itself.
_blocks = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'parser_blocks.txt')
BLOCKS = '00' if os.environ.get('BLOCKS_EMPTY') or not os.path.exists(_blocks) else open(_blocks).read().strip()
REGIONS = {
  # name: entry, S, exits, region hints, VRAM offset at entry
  'H': ('808F', 'FC', ['exit 8175', 'exit 8178'], ['frame', 'widen F2D0 FFF9', 'track 776', 'cell 776 0 1 80 81'] + STACK, None),
  'P': ('8175', 'FB', ['exit AF01'], PLAYER + STACK + [MIRROR], '0-30'),
  'E': ('AF01', 'F9', ['exit AF10'], ENEMY + STACK + RET + [MIRROR], '0-50'),
  'T': ('AF10', 'F9', ['exit AF67'], ['splitc 0 3', 'splity 89EF 89F9', 'splity 8600 8622'] + STACK + RET + [MIRROR], '0-a0'),
  'A': ('AF67', 'F9', ['exit 8178'], PARSER + STACK + RET + [MIRROR], '0-c0'),
  'Z': ('8178', 'FB', ['exit 808F'], ['frame'] + STACK + [MIRROR], None),
}
NEXT = {'8175': 'P', 'AF01': 'E', 'AF10': 'T', 'AF67': 'A', '8178': 'Z', '808F': 'H'}
glob = []
for line in open(bounds):
    w = line.split()
    # the block buffers hold whatever the level and the blocks hit put there
    if len(w) > 2 and w[0] == 'global' and w[2] != 'top' and int(w[1], 16) not in (0xE, 0x300, 0x340) and not 0x500 <= int(w[1], 16) <= 0x69F and int(w[1], 16) not in ALSO and (os.environ.get('NOPIN') or int(w[1], 16) not in PINS):
        glob.append(line.strip())
glob += [f'global {c:x} {v}' for c, v in ALSO.items()]
glob += [f'global {c:x} {BLOCKS}' for c in range(0x500, 0x6A0)]
# NOPIN leaves every bound to the generator, to see whether the code keeps them narrow by itself
if not os.environ.get('NOPIN'):
    glob += [f'global {c:x} {v}' for c, v in PINS.items()] + [f'pin {c:x}' for c in PINS]
# The parser reads no input, so its state follows one chain, whatever the player does: parser_chain.c records it, and the parser region's entries are that chain.
# Its exit states have to be on the chain again, and only it may write these cells, so the chain holds between its runs.
CHAIN = open(os.environ.get('PARSER_CHAIN') or os.path.join(os.path.dirname(os.path.abspath(__file__)), 'parser_chain.txt')).read().splitlines()
CELLS = CHAIN[0].split()[1:]
def chain_cases():
    rows = []
    for row in CHAIN[1:]:
        vals = [row[i:i + 2] for i in range(0, len(row), 2)]
        rows.append(' '.join(f'{c}={v}' for c, v in zip(CELLS, vals) if v != '..'))
    return ['case ' + r for r in rows]
TRACKED = [c for c in CELLS if not c.startswith('e')]
NCELLS = {int(c, 16) for c in CELLS}
def chain_bounds():
    # The other regions see the chain's cells as bounds. A cell the tail leaves out has no bound of its own: `OBJ` gives those a cell, or nothing does
    rows = []
    for i, c in enumerate(CELLS):
        vals = {row[2 * i:2 * i + 2] for row in CHAIN[1:]}
        if '..' not in vals:
            rows.append(f'global {c} ' + ' '.join(sorted(vals)))
    return rows
def is_chain_bound(l):
    return l.startswith('global ') and int(l.split()[1], 16) in NCELLS
KEEPS = ['prot ' + c for c in CELLS]
for name, (pc, s, ex, hints, v300) in REGIONS.items():
    cell300 = []  # the offsets' bounds are the run's assumption, `NoOverflow`
    nx = [f'next {e.split()[1]} {out}/{NEXT[e.split()[1]]}.cfg' for e in ex if e.split()[1] in NEXT]
    keep = KEEP if name != 'P' else []
    lines = [f'entry {pc} {s}'] + ex + COMMON + keep + hints + OBJ + cell300 + glob + nx + [f'saveg {out}/{name}.g', 'max 2000000', 'maxboxes F4240']
    if name == 'A':
        # it never touches the enemy list's cells, so they needn't split its entries
        drop = {'track 739', 'track 73b'}
        lines = [l for l in lines if not l.startswith('case ') and l not in drop and not is_chain_bound(l)]
        lines += chain_cases() + ['track ' + c for c in TRACKED] + ['splitc ' + ' '.join(CELLS), 'prot 739', 'prot 73b']
    else:
        lines = [l for l in lines if not is_chain_bound(l)] + chain_bounds() + KEEPS
    open(f'{out}/{name}.cfg', 'w').write('\n'.join(lines) + '\n')
print(len(glob), 'bounds')
