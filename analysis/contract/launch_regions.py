#!/usr/bin/env python3
"""Write one smbabs config per stretch of a frame during the launch at the start of 1-1: every enemy slot empty, the screen not scrolled, the parser idle.
PlayerCtrlRoutine from $B0E9 to $B179 isn't among them: Smb.Routine.ModelFrame has that. So nothing here may write Mario's cells.
usage: launch_regions.py OUTDIR"""
import sys
out = sys.argv[1]
DONE = '91BA 9277 B0D5 B1B8 B27A B8AA D948 DDFC DE75 DE86 DF01 FAEF 8031 82CB 82F2 8483 91E5 9260 927E DE15 82CE 82FD 845D 8475 874E 905D 90C8 91E0 9233 925A 9279 B218 D009 DE10'.split()
P = 'p 24 25 26 27 64 65 66 67 A4 A5 A6 A7 E4 E5 E6 E7'
STACK = ['cell 1fd 24 25 26 27 64 65 66 67 a4 a5 a6 a7 e4 e5 e6 e7', 'cell 1fe 57', 'cell 1ff 80']
MIRROR = ['cell 1fc 10 11 14 15']
RET = ['cell 1fa 77', 'cell 1fb 81']
# Mario's cells: the model's, the position and the screen's edges
# and `$0A`, whose A bit `SaveAB` copies to `$0D`, and `$0D`, which only region A may change
PROT = ['prot ' + c for c in '57 705 700 33 45 1D 703 CE 416 9F 433 709 70A 708 706 86 6D 400 A D'.split()] + ['prot 71A 71D', 'prot e', 'prot 770', 'prot 772']
# Constant through the launch. Each is a bound a write has to meet, so a write of anything else is an alarm where it happens.
CONST = {0xF: '0', 0x10: '0', 0x11: '0', 0x12: '0', 0x13: '0', 0x14: '0', 0x16: '0', 0x17: '0', 0x18: '0', 0x19: '0', 0x1A: '0', 0x1B: '0',
         0x71A: '0', 0x71B: '0', 0x71C: '0', 0x71D: 'ff', 0x739: '3', 0x73A: '1', 0x73B: '0', 0xE9: '1', 0xEA: '9f', 0x6CD: '0', 0x6CB: '0', 0x745: '0', 0x76A: '0', 0x74E: '1',
         0x398: '0', 0x758: '0', 0x770: '1', 0x772: '3', 0xE: '8', 0x71F: '0', 0x73D: '0', 0x704: '0', 0x70B: '0', 0x70E: '0', 0x753: '0', 0x77A: '0', 0x75F: '0', 0x760: '0', 0x747: '0', 0x756: '0', 0x6CC: '0', 0x490: 'ff', 0xB5: '1', 0x716: '0', 0x754: '1', 0x714: '0', 0x3A1: '0', 0x723: '0', 0x776: '0 1 80 81', 0x3EC: '0', 0x3ED: '0', 0x79F: '0', 0x6D: '0', 0x86: '0-4f', 0x755: '0-4f', 0x3AD: '0-4f', 0x778: '10 11 14 15', 0x779: '06 1e',
         **{a: '0' for a in range(0x24, 0x33)}, **{a: '0' for a in range(0x46B, 0x471)},
         # The block buffer where Mario can be: air down to the floor's two rows
         **{0x500 + r * 16 + c: ('54' if r >= 11 else '0') for r in range(13) for c in range(7)}}
COMMON = ['exit ' + d for d in DONE] + ['nes', P, 'track 0 F', 'track e0 ef', 'assume 300 00-34', 'assume 340 00-21', 'cell e 8', 'nogrow', 'promote 10000',
          'splita 8E04 8E18', 'splity 8E04 8E18', 'splita B76C B772', 'splita B79A B79D', 'track 6e 73', 'track 87 8c'] + PROT + [f'global {a:x} {v}' for a, v in CONST.items()]
REGIONS = {
  'H': ('808F', 'FC', ['exit 8175', 'exit 8178'], ['frame', 'splitc 0 3 8', 'widen F2D0 FFF9', 'track 776', 'cell 776 0 1 80 81'] + STACK),
  'Q': ('8175', 'FB', ['exit B0E9'], ['splitc 0 3 8'] + STACK + MIRROR),
  'R': ('B179', 'F7', ['exit AF01'], ['splitc 0 3 8', 'splity BDF6 BE01', 'splity 8F1C 8F3A', 'splita 8F11 8F1C', 'cell 1f8 f5', 'cell 1f9 ae'] + STACK + RET + MIRROR),
  'E': ('AF01', 'F9', ['exit AF10'], ['splitc 0 3 8', 'splity 89EF 89F9', 'splity 8600 8622', 'splity C120 C2A0', 'splity 8F1C 8F3A', 'splita 8F11 8F1C', 'splity C886 C88F'] + STACK + RET + MIRROR),
  'T': ('AF10', 'F9', ['exit AF67', 'exit B79A'], ['splitc 2 3', 'splitcr 0 89E1 8A40', 'splita B9CF B9D6', 'splity 89EF 89F9', 'splity 8600 8622'] + STACK + RET + MIRROR),
  'A': ('AF67', 'F9', ['exit AF6B'], ['splitc 0 3 8'] + STACK + RET + MIRROR),
  'B': ('AF6B', 'F9', ['exit 8178'], ['splitc 0 3 8'] + STACK + RET + MIRROR),
  'Z': ('8178', 'FB', ['exit 808F'], ['frame', 'splitc 0 3 8'] + STACK + MIRROR),
}
# What each region's exit has to satisfy. Q's exit is PlayerCtrlRoutine's entry, and R's entry its end: ModelFrame covers the stretch between.
NEXT = {'8175': 'Q', 'AF01': 'E', 'AF10': 'T', 'AF67': 'A', 'AF6B': 'B', '8178': 'Z', '808F': 'H'}
# R starts where the routine ends, whose summary only says the I flag is set, and that carries on until the handler's RTI restores them from the stack
ANYP = 'p ' + ' '.join(f'{v:02X}' for v in range(256) if v & 4)
for name, (pc, s, ex, hints) in REGIONS.items():
    nx = [f'next {e.split()[1]} {out}/{NEXT[e.split()[1]]}.cfg' for e in ex if e.split()[1] in NEXT]
    common = [ANYP if name in 'RETABZ' and l == P else l for l in COMMON if not (name == 'A' and l == 'prot D')] + (['prot 783'] if name in 'RETABZ' else [])
    open(f'{out}/{name}.cfg', 'w').write('\n'.join([f'entry {pc} {s}'] + ex + common + hints + nx + [f'saveg {out}/{name}.g', 'max 2000000', 'maxboxes F4240']) + '\n')
