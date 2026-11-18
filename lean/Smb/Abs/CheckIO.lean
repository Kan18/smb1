import Smb.Abs.Check

/-!
# The checker for code that touches hardware registers

The plain-machine checker `check` rejects an access outside RAM and ROM. On the full NES the game's reads of `$2002`, `$2007`
and `$4016` return values that depend on the PPU and the controllers, and its writes to the PPU and APU leave CPU RAM alone.
`checkN` accepts those instructions too, for every value read. `Smb.Routine.AbsIO` proves it sound on the full NES.
-/
namespace Smb.Abs

/-- The hardware-register stores of the game's code: `sta`, `stx`, `sty` absolute and `sta` absolute,X. -/
def ioKind : Kind → Bool
  | .store _ .abs | .store .a .absx => true
  | _ => false

/-- Loads treated as returning anything, wherever they read: `lda`, `ldx`, `ldy` absolute, their indexed forms, and `lda (zp),Y`.
No read on the bus changes a CPU register or RAM. -/
def anyLoad : Kind → Bool
  | .load _ .abs | .load .a .absx | .load .a .absy | .load .x .absy | .load .y .absx | .load .a .indy => true
  | _ => false

/-- The store leaves RAM, and does not turn on NMI generation: such a store is an exit of the table. -/
def ioAddrOk (k : Kind) (b1 b2 : UInt8) (r : Regs) : Bool :=
  let a := operandAddr k b1 b2 r 0 0
  0x2000 ≤ a && a < 0x8000 &&
  match k with
  | .store rg _ => 0x4000 ≤ a || a &&& 7 != 0 || regOf rg r.a r.x r.y &&& 0x80 == 0
  | _ => true

/-- Every state of `b` steps into the table, for any value read: the flags depend only on the value's sign and whether it is zero. -/
def loadCovers (g : Global) (b : Box) (k : Kind) (next : UInt16) (cand : Box) : Bool :=
  let isTop : VS → Bool := fun v => match v with | .top => true | _ => false
  cand.pc == next && cand.s == b.s &&
  (if writesA k then isTop cand.a else b.a.sub cand.a) &&
  (if writesX k then isTop cand.x else b.x.sub cand.x) &&
  (if writesY k then isTop cand.y else b.y.sub cand.y) &&
  b.p.elems.all (fun p => cand.p.mem (nz p 0) && cand.p.mem (nz p 1) && cand.p.mem (nz p 0x80)) &&
  cand.cells.all (cellCovered g b [])

def loadCoversFast (g : Global) (b : Box) (k : Kind) (next : UInt16) (cand : Box) : Bool :=
  let isTop : VS → Bool := fun v => match v with | .top => true | _ => false
  cand.pc == next && cand.s == b.s && cand.cells.all (cellCovered g b []) &&
  (if writesA k then isTop cand.a else b.a.sub cand.a) &&
  (if writesX k then isTop cand.x else b.x.sub cand.x) &&
  (if writesY k then isTop cand.y else b.y.sub cand.y) &&
  b.p.elems.all (fun p => cand.p.mem (nz p 0) && cand.p.mem (nz p 1) && cand.p.mem (nz p 0x80))

@[csimp] theorem loadCovers_eq_fast : loadCovers = loadCoversFast := by
  funext g b k next cand
  simp only [loadCovers, loadCoversFast, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm] <;> rfl

def loadBox (rom : UInt16 → UInt8) (g : Global) (T : Table) (b : Box) : Bool :=
  let k := decode (rom b.pc)
  let next := match k with
    | .load _ m => b.pc + m.size
    | _ => b.pc
  0x8000 ≤ b.pc && b.pc ≤ 0xFFF0 && anyLoad k &&
  b.p.elems.all (fun p => p &&& 4 != 0) &&
  (T.at next).any (loadCovers g b k next)

/-- Every state of `b` steps into the table, past the store. -/
def ioBox (rom : UInt16 → UInt8) (g : Global) (T : Table) (b : Box) : Bool :=
  let pc := b.pc
  let k := decode (rom pc)
  let b1 := rom (pc + 1)
  let b2 := rom (pc + 2)
  0x8000 ≤ pc && pc ≤ 0xFFF0 && ioKind k &&
  (regList (readsA k) b.a).all fun a =>
  (regList (readsX k) b.x).all fun x =>
  (regList (readsY k) b.y).all fun y =>
  b.p.elems.all fun p =>
    let r : Regs := ⟨pc, a, x, y, b.s, p⟩
    let e := eval k b1 b2 r 0 0 0
    ioAddrOk k b1 b2 r && e.regs.p &&& 4 != 0 &&
    (T.at e.regs.pc).any (covers g b k ⟨e.regs, []⟩ none 0)

/-- Ordinary instruction alternatives, in the order used by soundness proofs. -/
def checkAny (rom : UInt16 → UInt8) (prot : UInt16 → Bool) (g : Global) (T : Table) (b : Box) : Bool :=
  checkBox rom prot g T b || ioBox rom g T b || loadBox rom g T b

/-- Try the inexpensive unrestricted-load rule before enumerating concrete tuples. -/
def checkAnyFast (rom : UInt16 → UInt8) (prot : UInt16 → Bool) (g : Global) (T : Table) (b : Box) : Bool :=
  loadBox rom g T b || checkBox rom prot g T b || ioBox rom g T b

@[csimp] theorem checkAny_eq_fast : checkAny = checkAnyFast := by
  funext rom prot g T b
  simp only [checkAny, checkAnyFast, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

/-- As `check`, for the full NES: a box's instruction may also be a hardware access. -/
def checkN (rom : UInt16 → UInt8) (exit prot : UInt16 → Bool) (g : Global) (T : Table) : Bool :=
  (List.range 0x8000).all fun n =>
    (T.getD n []).all fun b =>
      (b.pc &&& 0x7FFF).toNat == n && 0x8000 ≤ b.pc &&
      (b.p.elems.all (fun p => p &&& 4 != 0)) &&
      (exit b.pc || checkAny rom prot g T b)

/-! ## Between frames

The handler ends with `sta $2000` at `$817E`, which turns NMI generation on, and `rti` at `$8181` back to the idle loop `jmp $8057`.
The next NMI enters at `$8082`, and NMI generation stays on until the `sta $2000` at `$808C`. `checkF` checks those instructions too,
so its table can close over frames.
-/

def onEnter : UInt16 := 0x817E
def rtiPC : UInt16 := 0x8181
def idlePC : UInt16 := 0x8057
def onExit : UInt16 := 0x808C

/-- The handler's first instructions, before NMI generation goes off. -/
def preamblePC (pc : UInt16) : Bool := pc == 0x8082 || pc == 0x8085 || pc == 0x8087 || pc == 0x808A || pc == onExit

/-- Addresses that run with NMI generation on. -/
def onPC (pc : UInt16) : Bool := pc == rtiPC || pc == idlePC || preamblePC pc

/-- What an NMI does to a state: push the return address and P, set I, jump through the vector. -/
def nmiEff (rom : UInt16 → UInt8) (r : Regs) : Eff :=
  ⟨⟨base (rom 0xFFFA) (rom 0xFFFB), r.a, r.x, r.y, r.s - 3, r.p ||| CPU.FI⟩,
   [(stack r.s, (r.pc >>> 8).toUInt8), (stack (r.s - 1), r.pc.toUInt8),
    (stack (r.s - 2), (r.p &&& ~~~CPU.FB) ||| CPU.FU)]⟩

/-- Every state of `b` can take an NMI, into the table. -/
def nmiBox (rom : UInt16 → UInt8) (prot : UInt16 → Bool) (g : Global) (T : Table) (b : Box) : Bool :=
  base (rom 0xFFFA) (rom 0xFFFB) == 0x8082 &&
  b.p.elems.all fun p =>
    let e := nmiEff rom ⟨b.pc, 0, 0, 0, b.s, p⟩
    e.wr.all (wrOk prot g) && (T.at e.regs.pc).any (covers g b .jsr e none 0)

/-- `sta $2000`, whose value does not matter: NMI generation may turn on. -/
def enterBox (rom : UInt16 → UInt8) (g : Global) (T : Table) (b : Box) : Bool :=
  let k := decode (rom b.pc)
  k == .store .a .abs && base (rom (b.pc + 1)) (rom (b.pc + 2)) == 0x2000 && onPC (b.pc + 3) &&
  b.a.elems.all fun a => b.p.elems.all fun p =>
    p &&& 4 != 0 && (T.at (b.pc + 3)).any (covers g b k ⟨⟨b.pc + 3, a, 0, 0, b.s, p⟩, []⟩ none 0)

/-- `sta $2000` with bit 7 clear: NMI generation goes off. -/
def exitBox (rom : UInt16 → UInt8) (g : Global) (T : Table) (b : Box) : Bool :=
  let k := decode (rom b.pc)
  k == .store .a .abs && base (rom (b.pc + 1)) (rom (b.pc + 2)) == 0x2000 &&
  b.a.elems.all (fun a => a &&& 0x80 == 0) && ioBox rom g T b

/-- The handler's first instructions: `lda` absolute, `and` immediate, `sta` absolute, `and` immediate. -/
def preambleOp (rom : UInt16 → UInt8) (pc : UInt16) : Bool :=
  (pc == 0x8082 && rom pc == 0xAD) || (pc == 0x8085 && rom pc == 0x29) ||
  (pc == 0x8087 && rom pc == 0x8D) || (pc == 0x808A && rom pc == 0x29)

/-- The stack holds exactly this return address. -/
def rtiToIdle (rom : UInt16 → UInt8) (g : Global) (b : Box) : Bool :=
  rom b.pc == 0x40 && (readVS rom g b (stack (b.s + 2))).elems == [0x57] && (readVS rom g b (stack (b.s + 3))).elems == [0x80]

def idleLoop (rom : UInt16 → UInt8) (prot : UInt16 → Bool) (g : Global) (T : Table) (b : Box) : Bool :=
  rom b.pc == 0x4C && base (rom (b.pc + 1)) (rom (b.pc + 2)) == idlePC && nmiBox rom prot g T b

def boxF (rom : UInt16 → UInt8) (exit prot : UInt16 → Bool) (g : Global) (T : Table) (b : Box) : Bool :=
  exit b.pc ||
  (if b.pc == onEnter then enterBox rom g T b
   else if b.pc == onExit then exitBox rom g T b
   else if b.pc == rtiPC then checkBox rom prot g T b && rtiToIdle rom g b
   else if b.pc == idlePC then checkBox rom prot g T b && idleLoop rom prot g T b
   else if preamblePC b.pc then checkBox rom prot g T b && preambleOp rom b.pc
   else checkAny rom prot g T b)

/-- As `checkN`, with the instructions between frames. -/
def checkF (rom : UInt16 → UInt8) (exit prot : UInt16 → Bool) (g : Global) (T : Table) : Bool :=
  (List.range 0x8000).all fun n =>
    (T.getD n []).all fun b =>
      (b.pc &&& 0x7FFF).toNat == n && 0x8000 ≤ b.pc &&
      (b.p.elems.all (fun p => p &&& 4 != 0)) && boxF rom exit prot g T b

end Smb.Abs
