#!/usr/bin/env python3
"""Frame-rule chain: for each intermediate-screen entry, V = W+20 has ITC 0. Check
   ticks(V1->V2) = 21*(ceil(tau/21)+K), where tau, K come from the limiting event, and print the slack."""
import csv, math, sys
from check import load
def run(fn):
    R = load(fn); n = len(R)
    def ticks(a, b):
        return sum(1 for i in range(a + 1, b + 1) if R[i]['itc'] != R[i-1]['itc'])
    As = sorted({i for i in range(1, n) if R[i]['mode'] == 1 and R[i]['task'] == 0 and (R[i-1]['task'] != 0 or R[i-1]['mode'] != 1)})
    Vs = []
    for A in As:
        at = (R[A]['aptr'] >> 5) & 3
        if R[A]['alt'] == 0 and (at == 3 or R[A]['dint'] == 0):
            W = next(i for i in range(A + 8, n) if R[i]['scr'] == 8)
            Vs.append((W + 20, A))
    print(fn, 'anchors V (first frame with ITC=0 after the intermediate screen):', [v for v, _ in Vs], 'ITC:', [R[v]['itc'] for v, _ in Vs if v < n])
    print(' from->to      A   limiter      tau  j   slack  gain  ticks(pred/act)  frames lag frz ok')
    bad = sum(R[v]['itc'] != 0 for v, _ in Vs if v < n)
    if len(Vs) < 2:
        raise ValueError(f'{fn}: need at least two completed anchors')
    for (V1, _), (V2, A) in zip(Vs, Vs[1:]):
        lagf = sum(1 for i in range(V1 + 1, V2 + 1) if R[i]['polls'] == 0)
        frz = sum(1 for i in range(V1 + 1, V2 + 1) if R[i]['itc'] == R[i-1]['itc'] and R[i]['polls'] != 0)
        act = ticks(V1, V2)
        ges_prev = R[A]['ges']
        if ges_prev == 5:     # flag
            s4 = next(i for i in range(A, V1, -1) if R[i]['star'] < 4) + 1
            s5 = A - 1
            ms = next((i for i in range(V1, A) if R[i]['mus'] == 32), None)
            me = next((i for i in range(ms, A + 1) if R[i]['mus'] == 0), None) if ms else None
            tau = ticks(V1, s4)
            j = math.ceil(tau / 21)
            pred = 21 * (j + 13)
            name = f'flag s4={s4}'
            K = 13
        elif ges_prev == 3:   # warp pipe
            G = A - 48
            tau = ticks(V1, G) + 56
            j = math.ceil(tau / 21)
            pred = 21 * (j + 7)
            name = f'warp G={G}'
        else:                 # e.g. PlayerLoseLife etc.: use A itself
            tau = ticks(V1, A) + 8
            j = math.ceil(tau / 21)
            pred = 21 * (j + 7)
            name = f'ges={ges_prev}'
        slack = 21 * j - tau
        ok = pred == act and (act % 21 == 0) and V2 - V1 == act + lagf + frz
        bad += not ok
        print(f'  {V1:6d}->{V2:6d} {A:6d} {name:16s} {tau:6d} {j:4d} {slack:3d} {21-slack:3d}   {pred}/{act}  {V2-V1} {lagf} {frz} {ok}')
    print(fn, 'chain mismatches', bad)
    # freezes by TC
    i = 1; ev = []
    while i < n:
        if R[i]['tc'] and not R[i-1]['tc']:
            j = i
            while j < n and R[j]['tc']: j += 1
            ev.append((i, j - i, R[i]['ges']))
            i = j
        else: i += 1
    print(fn, 'TimerControl runs (frame, length, GES):', ev)
    return bad

if __name__ == '__main__':
    if len(sys.argv) < 2:
        sys.exit('usage: chain.py TRACE.csv [TRACE.csv ...]')
    failures = sum(run(fn) for fn in sys.argv[1:])
    sys.exit(1 if failures else 0)
