"""Code facts for a routine proof, taken from the ROM instead of copied by hand.

  routine.py gen ENTRY --until A[,B...] [--call X,...] [--skip X,...] [--table ADDR:LEN ...] [--name NAME]
      Traces the code reachable from ENTRY (branches both ways, JSR into the callee and on
      after it, JMP; ends at RTS/RTI, at the `until` addresses and at indirect jumps) and
      prints: the ROM excerpt definitions (one per contiguous range, tables given by --table
      merged in), the `CodeAt` hypotheses, the `hstop` ranges (executed code and the `until`
      addresses), and the `until` list for `sym_run` in decimal. Callees in --call (entry
      addresses that have call theorems) are not traced, but their RTS bytes are not needed
      either. Code in --skip (e.g. a path the theorem excludes by hypothesis) is not traced.
      Gaps of up to 3 bytes between ranges are filled from the ROM. Warns about every ROM table the code reads that the ranges do not cover, and
      about indirect jumps.
  routine.py check FILE.lean...
      Checks local `smbPrg%` definitions used as `CodeAt prg 0xOFFS NAME` against the ROM.

Addresses are hex (`B8BD`, `$B8BD`, `0xB8BD`).
"""
import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ROM = (ROOT / "Super Mario Bros. (World).nes").read_bytes()[16:16 + 0x8000]

# 6502 official opcodes: opcode -> (mnemonic, mode). Modes: imp acc imm zp zpx zpy abs abx aby
# ind izx izy rel.
_T = """
00 brk imp 01 ora izx 05 ora zp 06 asl zp 08 php imp 09 ora imm 0a asl acc 0d ora abs 0e asl abs
10 bpl rel 11 ora izy 15 ora zpx 16 asl zpx 18 clc imp 19 ora aby 1d ora abx 1e asl abx
20 jsr abs 21 and izx 24 bit zp 25 and zp 26 rol zp 28 plp imp 29 and imm 2a rol acc 2c bit abs
2d and abs 2e rol abs 30 bmi rel 31 and izy 35 and zpx 36 rol zpx 38 sec imp 39 and aby 3d and abx
3e rol abx 40 rti imp 41 eor izx 45 eor zp 46 lsr zp 48 pha imp 49 eor imm 4a lsr acc 4c jmp abs
4d eor abs 4e lsr abs 50 bvc rel 51 eor izy 55 eor zpx 56 lsr zpx 58 cli imp 59 eor aby 5d eor abx
5e lsr abx 60 rts imp 61 adc izx 65 adc zp 66 ror zp 68 pla imp 69 adc imm 6a ror acc 6c jmp ind
6d adc abs 6e ror abs 70 bvs rel 71 adc izy 75 adc zpx 76 ror zpx 78 sei imp 79 adc aby 7d adc abx
7e ror abx 81 sta izx 84 sty zp 85 sta zp 86 stx zp 88 dey imp 8a txa imp 8c sty abs 8d sta abs
8e stx abs 90 bcc rel 91 sta izy 94 sty zpx 95 sta zpx 96 stx zpy 98 tya imp 99 sta aby 9a txs imp
9d sta abx a0 ldy imm a1 lda izx a2 ldx imm a4 ldy zp a5 lda zp a6 ldx zp a8 tay imp a9 lda imm
aa tax imp ac ldy abs ad lda abs ae ldx abs b0 bcs rel b1 lda izy b4 ldy zpx b5 lda zpx b6 ldx zpy
b8 clv imp b9 lda aby ba tsx imp bc ldy abx bd lda abx be ldx aby c0 cpy imm c1 cmp izx c4 cpy zp
c5 cmp zp c6 dec zp c8 iny imp c9 cmp imm ca dex imp cc cpy abs cd cmp abs ce dec abs d0 bne rel
d1 cmp izy d5 cmp zpx d6 dec zpx d8 cld imp d9 cmp aby dd cmp abx de dec abx e0 cpx imm e1 sbc izx
e4 cpx zp e5 sbc zp e6 inc zp e8 inx imp e9 sbc imm ea nop imp ec cpx abs ed sbc abs ee inc abs
f0 beq rel f1 sbc izy f5 sbc zpx f6 inc zpx f8 sed imp f9 sbc aby fd sbc abx fe inc abx
"""
OPS = {}
_w = _T.split()
for i in range(0, len(_w), 3):
    OPS[int(_w[i], 16)] = (_w[i + 1], _w[i + 2])
LEN = {"imp": 1, "acc": 1, "imm": 2, "zp": 2, "zpx": 2, "zpy": 2, "izx": 2, "izy": 2, "rel": 2,
       "abs": 3, "abx": 3, "aby": 3, "ind": 3}


def rom(a):
    return ROM[(a - 0x8000) & 0x7FFF]


def addr(s):
    s = s.strip()
    if not re.fullmatch(r"(?:\$|0x)?[0-9A-Fa-f]{4}", s):
        raise SystemExit(f"expected a four-digit hexadecimal address: {s}")
    return int(s.removeprefix("$").removeprefix("0x"), 16)


def trace(entry, until, calls, skip=()):
    code, reads, warns = set(), {}, []
    todo, seen = [entry], set()
    while todo:
        pc = todo.pop()
        if pc in seen or pc in until or pc in skip:
            continue
        seen.add(pc)
        op = rom(pc)
        if op not in OPS:
            warns.append(f"unofficial opcode ${op:02X} at ${pc:04X}")
            continue
        mn, mode = OPS[op]
        n = LEN[mode]
        code.update(range(pc, pc + n))
        nxt = pc + n
        operand = rom(pc + 1) | rom(pc + 2) << 8 if n == 3 else rom(pc + 1)
        if mode in ("abs", "abx", "aby") and operand >= 0x8000 and mn not in ("jsr", "jmp"):
            reads.setdefault(operand, (mode, pc))
        if mn in ("rts", "rti", "brk"):
            continue
        if mn == "jmp":
            if mode == "ind":
                warns.append(f"indirect jump at ${pc:04X}: split on its target, trace targets separately")
            else:
                todo.append(operand)
            continue
        if mn == "jsr":
            if operand not in calls:
                todo.append(operand)
            if operand == 0x8E04:  # JumpEngine on the target cartridge
                warns.append(f"JumpEngine at ${pc:04X}: its table follows the JSR; trace the targets separately")
                continue
            todo.append(nxt)
            continue
        if mode == "rel":
            off = rom(pc + 1)
            todo.append((nxt + (off - 256 if off >= 128 else off)) & 0xFFFF)
        todo.append(nxt)
    return code, reads, warns


def ranges(addrs, gap=0):
    out = []
    for a in sorted(addrs):
        if out and a <= out[-1][1] + 1 + gap:
            out[-1][1] = a
        else:
            out.append([a, a])
    return out


def gen(args):
    entry = addr(args[0])
    until, calls, skip, tables, name = [], [], [], [], "routine"
    i = 1
    while i < len(args):
        if args[i] == "--until":
            until = [addr(x) for x in args[i + 1].split(",")]
        elif args[i] == "--call":
            calls = [addr(x) for x in args[i + 1].split(",")]
        elif args[i] == "--skip":
            skip = [addr(x) for x in args[i + 1].split(",")]
        elif args[i] == "--table":
            a, n = args[i + 1].split(":")
            tables.append((addr(a), int(n, 0)))
        elif args[i] == "--name":
            name = args[i + 1]
        i += 2
    code, reads, warns = trace(entry, set(until), set(calls), set(skip))
    with_tables = set(code)
    for a, n in tables:
        with_tables.update(range(a, a + n))
    rs = ranges(with_tables, gap=3)
    covered = {a for lo, hi in rs for a in range(lo, hi + 1)}
    for a, (mode, pc) in sorted(reads.items()):
        if a not in covered:
            warns.append(f"reads ROM at ${a:04X} ({mode}, from ${pc:04X}) outside the code ranges:"
                         f" add --table {a:04X}:LEN if the proof needs its values")
    print("import Smb.Data.ProofRom")
    print(f"-- entry ${entry:04X}, until {', '.join(f'${u:04X}' for u in until)}")
    hyps = []
    for k, (lo, hi) in enumerate(rs):
        nm = name if len(rs) == 1 else f"{name}{k}"
        print(f"\n/-- `${lo:04X}`–`${hi:04X}`. -/\ndef {nm}Code : List UInt8 :=\n  smbPrg% 0x{lo:04X} {hi - lo + 1}")
        hyps.append(f"(h{k}code : CodeAt prg 0x{lo - 0x8000:04X} {nm}Code)")
    print("\n-- hypotheses:\n" + "\n".join("    " + h for h in hyps))
    executed = set(code)
    for c in calls:  # the callee runs too: its code must avoid the caller's stop address
        executed |= trace(c, set(), set())[0]
    stop = ranges(executed | set(until), gap=3)
    print("\n-- hstop: ∀ a : UInt16, (" + " || ".join(
        f"0x{lo:04X} ≤ a && a ≤ 0x{hi:04X}" if lo != hi else f"a == 0x{lo:04X}" for lo, hi in stop) + ") = true → a ≠ stop")
    print(f"-- sym_run … until {until[0] if len(until) == 1 else list(until)}")
    if calls:
        print("-- calls (not traced): " + ", ".join(f"${c:04X}" for c in calls))
    for w in warns:
        print("-- WARNING: " + w)


def check(files):
    bad = n = 0
    for p in files:
        src = Path(p).read_text()
        defs = {
            name: (int(address, 16) - 0x8000, int(length))
            for name, address, length in re.findall(
                r"def (\w+) : List UInt8 :=\s*smbPrg%\s+(0x[0-9A-Fa-f]+)\s+([0-9]+)", src
            )
        }
        for m in re.finditer(r"CodeAt prg 0x([0-9A-Fa-f]+) (\w+)\b", src):
            off, nm = int(m.group(1), 16), m.group(2)
            if nm not in defs:
                continue
            start, length = defs[nm]
            n += 1
            if not (0 <= start < start + length <= len(ROM) and 0 <= off <= len(ROM) - length):
                print(f"{p}: {nm} has a range outside PRG ROM")
                bad += 1
            elif ROM[start:start + length] != ROM[off:off + length]:
                print(f"{p}: {nm} at ${start + 0x8000:04X} differs from the ROM at ${off + 0x8000:04X}")
                bad += 1
    print(f"checked {n} code lists in {len(files)} files, {bad} mismatches")
    return bad


if __name__ == "__main__":
    if sys.argv[1] == "gen":
        gen(sys.argv[2:])
    elif sys.argv[1] == "check":
        sys.exit(1 if check(sys.argv[2:]) else 0)
    else:
        print(__doc__)
