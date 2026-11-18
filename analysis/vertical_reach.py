"""Over-approximate reachability of Mario's vertical state, for the floor-clip question.

Usage: python3 analysis/vertical_reach.py ROM [--vine]

Abstract state: (position mod 16 px with sub-pixel, 8.8 velocity, active gravity, fall
gravity). Moves, each allowed whenever plausible (so this over-approximates play on land):
jump start (any class 0-4: sub-pixel and force reset, table speed and gravities), A held or
released while rising, gravity per frame (exactly `gravityVel` with max 4), stomp bounce
(speed byte $FC/$FD, force kept), head bump (speed byte $01/$00/$FE, force kept), jumpspring
bounce after a landing (speed $F9/$F4, force 0, gravity $70, at any row offset: the spring moves
Mario by 2 px per frame before the bounce), landing on any row
entry with offset < 5 (speed/force 0, Y aligned, sub-pixel kept) followed by a jump or by
walking off (falling gravity), and with --vine: grabbing a vine anywhere, climbing
(sub += $20/$FF/0 per frame) and stepping off into a fall.

A "skip" is a falling frame whose feet enter a new metatile row at offset >= 5, i.e. Mario
passes the landing window (`floor_skip_iff` in lean/Smb/Routine/FloorClip.lean).

The land model reaches 2,499,968 states and has no skip. At speed 5 the velocity's
fractional byte is 0 or 8. With an 8, the position's fractional byte is a multiple
of 16. Allowing vine transitions produces skips in this abstraction at velocity
$050F, row offset 15, and position fraction at least $F1.
"""
# Over-approximate reachability of Mario's vertical state (land, no vines/water).
# State: (pos12 = (Y & 15) << 8 | sub-pixel, vel16, vf (active gravity), vfd (fall gravity)).
# Semantics of gravity/position from the Lean definitions gravityVel / nextPos (A = 0, max 4).
import argparse
from collections import deque
from pathlib import Path

def sle(a, b):  # signed byte compare a <= b
    a = a - 256 if a >= 128 else a
    b = b - 256 if b >= 128 else b
    return a <= b

def gravity(down, v, mx=4):
    v1 = (v + down) & 0xFFFF
    if sle(mx, (v1 >> 8) & 0xFF) and (v1 & 0xFF) >= 0x80:
        v1 = mx << 8
    return v1

def sext(v): return v - 0x10000 if v >= 0x8000 else v

parser = argparse.ArgumentParser(description="Search reachable vertical states.")
parser.add_argument("rom", type=Path, help="Super Mario Bros. (World) iNES ROM")
parser.add_argument("--vine", action="store_true")
args = parser.parse_args()
raw = args.rom.read_bytes()
if raw[:6] != b"NES\x1a\x02\x01" or len(raw) != 16 + 0x8000 + 0x2000 or raw[6] & 4:
    raise SystemExit("expected Super Mario Bros. (World) as a trainerless iNES ROM")
JUMP = raw[0x3434:0x3439]  # PRG at CPU $B424
FALL = raw[0x343B:0x3440]  # $B42B
YSPD = raw[0x3442:0x3447]  # $B432
GRAV = sorted(set(JUMP + FALL) | {0x28})      # 0x28: game routine $0B / entrance

def jumps():
    for c in range(5):
        for off in range(16): yield (off << 8, YSPD[c] << 8, JUMP[c], FALL[c])

hits = []
seen = set()
q = deque()
def push(s):
    if s not in seen:
        seen.add(s); q.append(s)

for s in jumps(): push(s)
# walking off a ledge right after any landing is added on landing below

VINE = args.vine
CLIMB = [(0x00, 0x00), (0xFF, 0x20), (0x01, 0xFF)]   # (speed, force) for none / up / down
while q:
    st = q.popleft()
    if st[0] == 'vine':
        _, pos, d, vfd = st
        spd, frc = CLIMB[d]
        # ClimbingSub (proved): sub-pixel += force, pixel += sign-extended speed + carry.
        npos = (pos + frc + (spd - 256 if spd >= 0x80 else spd) * 256) & 0xFFF
        for d2 in range(3):
            push(('vine', npos, d2, vfd))
        # step off the vine: fall with the last climbing speed/force (FallingSub: gravity vfd)
        s2, f2 = CLIMB[d]
        push((npos, (s2 << 8) | f2, vfd, vfd))
        continue
    pos, v, vf, vfd = st
    if VINE:
        for d in range(3): push(('vine', pos, d, vfd))
    # gravity choice this frame: rising keeps vf only while A is held -> allow both
    choices = {vfd} if v < 0x8000 else {vf, vfd}
    for g in choices:
        newpos = pos + sext(v)            # in units of 1/256 px, relative
        y_old = pos >> 8; y_new = newpos >> 8
        rows_old = y_old >> 4; rows_new = y_new >> 4
        off_new = y_new & 15
        if v < 0x8000 and rows_new != rows_old:
            if off_new >= 5:
                hits.append((pos, v, g, vfd))
            else:
                # may land: speed/force 0, Y aligned (off 0), sub kept
                sub = newpos & 0xFF
                for off in range(16): push(((off << 8) | sub, 0, vfd, vfd))  # walk off (any offset: lifts)
                for s in jumps(): push(s)         # jump again (sub reset)
                # jumpspring: lands aligned (force 0, sub kept, VerticalForce := $70), then
                # JumpspringHandler moves Y by +-2 px per frame and bounces with speed $F9 or $F4
                # (with A). This model allows any row offset at launch.
                for js in (0xF9, 0xF4):
                    for off in range(16): push(((off << 8) | sub, js << 8, 0x70, vfd))
        nv = gravity(g, v)
        npos = newpos & 0xFFF                    # position mod 16 px
        push((npos, nv, g, vfd))
        # stomp bounce while falling: speed byte := $FC or $FD, force kept
        if nv < 0x8000:
            for sp in (0xFC, 0xFD):
                push((npos, (sp << 8) | (nv & 0xFF), g, vfd))
        # head bump while rising, force kept: NYSpd ($01), BumpBlock ($00), BrickShatter ($FE)
        if nv >= 0x8000:
            for hb in (0x01, 0x00, 0xFE):
                push((npos, (hb << 8) | (nv & 0xFF), g, vfd))
    if len(seen) > 30_000_000: print("too many states"); break

print("states", len(seen))
seen = {x for x in seen if x[0] != 'vine'}
speed5 = [(p, v) for (p, v, vf, vfd) in seen if 0x500 <= v <= 0x5FF]
print("speed-5 states", len(speed5), "distinct (sub-speed, sub-pixel mod 16?)",
      sorted({(v & 0xFF, p & 0xFF) for p, v in speed5})[:40])
print("skips", len(hits), hits[:10])
res = {}
for (p, v, vf, vfd) in seen:
    key = (vf, vfd)
    res.setdefault(key, set()).add(((p & 0xFF) % 16, (v & 0xFF) % 16))
for k in sorted(res):
    print(hex(k[0]), hex(k[1]), sorted(res[k]))
print("all (sub%16, force%16):", sorted({((p&0xFF)%16, (v&0xFF)%16) for (p,v,vf,vfd) in seen}))
