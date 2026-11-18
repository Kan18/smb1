# Mario's vertical physics, transcribed from the ROM (ProcJumping/InitJS, JumpSwimSub, FallingSub, and ImposeGravity
# with MovePlayerVertically's maximum speed 4), and two checks used in docs/later-levels.md:
#   python3 vertical_physics.py ROM entries  - every jump (5 speed classes, A held 1-45 frames, any start surface) and
#       every walk-off (down force of any class, any sub-pixel counter left by a landing): how deep the feet get into
#       the first surface they reach on the way down. The foot code lands Mario at depth 0-4 and lets him sink at 5+.
#   python3 vertical_physics.py ROM hang     - for a block face caught sideways with the feet 5-7 px below its top while
#       not rising, the longest run of frames the feet stay 5-15 px in (one 1-px foot push per frame).
# Checked against the emulator: standing jumps of 1, 3, 8, 20 and 40 frames of A from 1-2's ?-block row match frame
# for frame until landing. analysis/buffer/vertical_steps.c extends `entries` with every mid-air speed write.
import sys
from pathlib import Path
from struct import unpack

def step(s,force):
    y,sp,mf,dm=s
    dm2=dm+mf; c1=dm2>>8; dm2&=255
    y2=y+sp+c1
    mf2=mf+force; c2=mf2>>8; mf2&=255
    sp2=sp+c2
    if sp2>=4 and mf2>=0x80: sp2=4; mf2=0
    return (y2,sp2,mf2,dm2)
def jump(c,h,y0,frames=80):
    """A held for h frames counting the takeoff frame; yields y after each frame."""
    s=(y0,YS[c],0,0); force=JF[c]; down=FF[c]; out=[]
    for t in range(frames):
        if t>0:
            sp=s[1]
            if sp>=0: force=down
            elif t<h: pass                       # A held this frame and the previous one
            elif y0-s[0]<1: pass
            else: force=down
        s=step(s,force); out.append(s)
    return out
def walkoff(c,dm,y0,frames=60):
    s=(y0,0,0,dm); down=FF[c]; out=[]
    for t in range(frames):
        s=step(s,down); out.append(s)
    return out

def first_entry(traj, ys):
    prev = None
    for s in traj:
        if prev is not None and s[0] >= ys and prev[0] < ys:
            return prev, s, s[0] - ys
        prev = s
    return None

def entries():
    dist = {}; landdm = set()
    for c in range(5):
        for h in range(1, 46):
            for r0 in range(3, 12):
                y0 = 16 * r0; tr = [(y0, 0, 0, 0)] + jump(c, h, y0, 120)
                for r in range(r0 - 4, 12):
                    ys = 16 * r
                    if ys <= min(s[0] for s in tr): continue
                    e = first_entry(tr, ys)
                    if not e or e[0][1] < 0: continue
                    dist[e[2]] = dist.get(e[2], 0) + 1
                    if e[2] < 5: landdm.add((c, e[1][3]))
    print('jumps, entries by depth:', dict(sorted(dist.items())))
    seen = set(landdm); todo = list(landdm); wdist = {}
    while todo:
        c, dm = todo.pop()
        for r0 in range(3, 12):
            for r in range(r0 + 1, 12):
                e = first_entry([(16 * r0, 0, 0, dm)] + walkoff(c, dm, 16 * r0, 120), 16 * r)
                if not e: continue
                wdist[e[2]] = wdist.get(e[2], 0) + 1
                if e[2] < 5 and (c, e[1][3]) not in seen: seen.add((c, e[1][3])); todo.append((c, e[1][3]))
    print('walk-offs, entries by depth:', dict(sorted(wdist.items())))

def hang():
    best = {}
    for c in range(5):
        for h in range(1, 46):
            for r0 in range(4, 12):
                y0 = 16 * r0; tr = [(y0, 0, 0, 0)] + jump(c, h, y0, 120)
                for t in range(y0 - 112, y0 + 16, 16):
                    for i in range(1, len(tr)):
                        if not (5 <= tr[i][0] - t <= 7) or tr[i][1] < 0: continue
                        n = 0
                        for j in range(i, len(tr)):
                            if 5 <= tr[j][0] - t <= 15: n += 1
                            else: break
                        if n > best.get((t - y0) // 16, (0,))[0]: best[(t - y0) // 16] = (n, c, h, y0)
    for k in sorted(best): print(f'block top {k:+d} rows from the start surface: {best[k][0]} frames', best[k][1:])

if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[2] not in {'entries', 'hang'}:
        raise SystemExit("usage: vertical_physics.py ROM {entries,hang}")
    raw = Path(sys.argv[1]).read_bytes()
    if raw[:6] != b"NES\x1a\x02\x01" or len(raw) != 16 + 0x8000 + 0x2000 or raw[6] & 4:
        raise SystemExit("expected Super Mario Bros. (World) as a trainerless iNES ROM")
    JF = raw[0x3434:0x3439]  # PRG at CPU $B424
    FF = raw[0x343B:0x3440]  # $B42B
    YS = unpack("5b", raw[0x3442:0x3447])  # $B432
    {'entries': entries, 'hang': hang}[sys.argv[2]]()
