#!/usr/bin/env python3
"""Check the transition formulas against every transition in a trace from ftrace.c.
Trace rows describe the state after each zero-based frame. A is the frame on
which OperMode_Task becomes 0 in game mode. C is the first frame whose input
reaches PlayerCtrlRoutine. See docs/frame-timing.md for the formulas."""
import csv, sys
def load(fn):
    rows = list(csv.DictReader(open(fn)))
    result = [{k: int(v) for k, v in r.items()} for r in rows]
    if not result or any(r['frame'] != i for i, r in enumerate(result)):
        raise ValueError(f'{fn}: expected nonempty contiguous frames starting at zero')
    return result
def entry_e(y0, alt):
    # frames GES stays 7: table derived from PlayerEntrance; 96 for pipe exits rising from $F0 to $90
    if alt == 2: return 96
    if y0 >= 0x30: return 1
    return {0x20: 17, 0: 24}.get(y0)
def predict_from_A(R, A):
    s = R[A]
    atype = (s['aptr'] >> 5) & 3
    inter = s['alt'] == 0 and (atype == 3 or s['dint'] == 0)
    p = {'inter': inter, 'ia_end': A + 2}
    if inter:
        r = (s['itc'] - 7) % 21
        W = A + 8 + (r + 1) + 6 * 21
        p['W'] = W
        base = W + 18
    else:
        base = A + 26
    p['ges7'] = base
    return p
def check(fn):
    R = load(fn)
    nm = len(R)
    if nm < 9 or any(r['nmis'] > 1 for r in R):
        raise ValueError(f'{fn}: checker requires >=9 frames and at most one observed NMI entry per frame')
    bad = 0; n = 0; tick_bad = 0
    # 1. Tick law
    ticks = 0; wrapped = 0
    for i in range(1, nm):
        a, b = R[i-1], R[i]
        if b['frame'] < 8: continue
        ran = b['nmis'] > 0
        # expected ITC move
        paused_before = a['pause'] & 1
        exp = a['itc']
        # pause status is updated inside the handler before the test, so use b's bit
        tc0 = a['tc']
        if ran and not (b['pause'] & 1):
            if tc0 == 0 or tc0 == 1:
                exp = 20 if a['itc'] == 0 else a['itc'] - 1
        if exp != b['itc']:
            tick_bad += 1
            if tick_bad < 10: print('  tick law mismatch at', b['frame'], a['itc'], b['itc'], 'tc', tc0, 'pause', b['pause'], 'lag', b['polls'] == 0)
    print(f'{fn}: tick law checked on {nm-8} frames, mismatches {tick_bad}')
    # 2. A -> C
    As = [i for i in range(1, nm) if R[i]['mode'] == 1 and R[i]['task'] == 0 and R[i-1]['task'] != 0 or (R[i]['mode'] == 1 and R[i]['task'] == 0 and R[i-1]['mode'] != 1)]
    As = sorted(set(As))
    rows = []
    for A in As:
        p = predict_from_A(R, A)
        # actual
        g7 = next((i for i in range(A + 1, nm) if R[i]['ges'] == 7 and R[i]['task'] == 3), None)
        g8 = next((i for i in range(A + 1, nm) if R[i]['ges'] == 8 and R[i]['task'] == 3), None)
        w = None
        if p['inter']:
            w = next((i for i in range(A + 8, nm) if R[i]['scr'] == 8), None)
        lags = sum(1 for i in range(A + 1, (g7 or A + 1) + 1) if R[i]['polls'] == 0)
        seq_ok = R[A+2]['task'] == 1 and R[A+2]['scr'] == 0 and R[A+2]['polls'] == 0 and R[A+3]['scr'] == 1 and R[A+7]['scr'] == 6
        ok = g7 == p['ges7'] and seq_ok and lags == 1 and (not p['inter'] or w == p['W'])
        y0 = R[g7]['y'] if g7 else -1
        alt = R[g7]['alt'] if g7 else -1
        e = None; eok = True
        C = None
        if g8 is not None and g7 is not None and R[g7]['ectrl'] not in (6, 7):
            e = g8 - g7; C = g8 + 1
            pe = entry_e(y0, alt)
            eok = pe == e
        n += 1
        if not ok or not eok: bad += 1
        rows.append((A, R[A]['world']+1, R[A]['level']+1, R[A]['area'], R[A]['alt'], R[A]['dint'], R[A]['itc'], p['inter'], p.get('W'), w, g7, p['ges7'], e, C, R[C]['itc'] if C and C < nm else None, ok, eok))
    print(' A  w-l area alt dint itc inter Wpred Wact g7act g7pred e C itc(C) ok eok')
    for r in rows: print(' ', *r)
    print(f'{fn}: A->C transitions {n}, mismatches {bad}')
    # 3. pipe triggers G -> A
    pb = 0; pn = 0
    for i in range(1, nm):
        if R[i]['ges'] in (2, 3) and R[i-1]['ges'] not in (2, 3) and R[i]['task'] == 3:
            A = next((j for j in range(i, nm) if R[j]['task'] == 0), None)
            cat = R[i]['cat']; ok = A == i + cat
            pn += 1; pb += not ok
            print(f"  pipe ges={R[i]['ges']} G={i} cat={cat} A={A} pagex={R[i]['page']}:{R[i]['x']} itc={R[i]['itc']} ok={ok}")
    print(f'{fn}: pipe G->A {pn}, mismatches {pb}')
    # 4. Flag sequence
    fb = 0; fn2 = 0
    for i in range(1, nm):
        if R[i]['task'] == 3 and R[i]['ges'] in (4, 5) and R[i-1]['ges'] not in (4, 5):
            G = i
            S = next(j for j in range(G, nm) if R[j]['ges'] == 5)
            D = next(j for j in range(G, nm) if R[j]['star'] >= 1)
            s3 = next(j for j in range(D, nm) if R[j]['star'] >= 3)
            s4 = next(j for j in range(s3, nm) if R[j]['star'] >= 4)
            s5 = next(j for j in range(s4, nm) if R[j]['star'] >= 5)
            A = next(j for j in range(s5, nm) if R[j]['task'] == 0)
            T = R[D]['tmr']
            digit = T % 10
            fw = {1: 1, 3: 3, 6: 6}.get(digit, 0)
            ms = next((j for j in range(G, nm) if R[j]['mus'] == 32), None)
            me = next((j for j in range(ms, nm) if R[j]['mus'] == 0), None) if ms else None
            w5 = s4 + R[s4]['itc'] + 1 + 5 * 21
            # F(n) = 32(n-1) + d, d in {0,1} (d = 1 when n = 1); see REPORT section 4
            Fok = (s4 - s3 - 32) in ({0} if fw == 0 else {1} if fw == 1 else {32 * (fw - 1), 32 * (fw - 1) + 1})
            ok = s3 == D + T + 1 and Fok and s5 == max(w5, me or 0) and A == s5 + 1
            fn2 += 1; fb += not ok
            print(f"  flag G={G} world={R[G]['world']+1}-{R[G]['level']+1} yG={R[G]['y']} size={R[G]['size']} S-G={S-G} D-S={D-S} T={T} digit={digit} s3-D={s3-D} s4-s3={s4-s3} itc(s4)={R[s4]['itc']} w5={w5} s5={s5} music=[{ms},{me}] len={me-ms if me else None} A={A} ok={ok}")
    print(f'{fn}: flag sequences {fn2}, mismatches {fb}')
    # 5. game timer period
    prev = None; per = {}
    for i in range(1, nm):
        if R[i]['tmr'] != R[i-1]['tmr'] and R[i]['tmr'] == R[i-1]['tmr'] - 1 and R[i]['ges'] == 8 and R[i]['tc'] == 0:
            if prev is not None:
                d = i - prev; per[d] = per.get(d, 0) + 1
            prev = i
        elif R[i]['ges'] != 8: prev = None
    print(f'{fn}: game timer periods in GES=8 frames', per)
    return tick_bad + bad + pb + fb

if __name__ == '__main__':
    if len(sys.argv) < 2:
        sys.exit('usage: check.py TRACE.csv [TRACE.csv ...]')
    failures = sum(check(fn) for fn in sys.argv[1:])
    sys.exit(1 if failures else 0)
