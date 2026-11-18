import Smb.Regs

/-
The 6502 instruction semantics, written once against an abstract bus.

`Bus σ` supplies the CPU registers stored in a machine state `σ`, one bus read or write
(each one CPU cycle, with whatever side effects the machine attaches to it), and the
interrupt lines. `Smb.Nes` instantiates it with the full NES (PPU timing, DMA, NMI);
`Smb.Plain` instantiates it with bare RAM and ROM for routine-level proofs. Because both
run this same code, relating them only requires relating their bus operations
(`Smb.Refine`).

Official opcodes and NOP variants are implemented. Anything else, and clearing the I flag
(IRQs are not modelled), is reported through `Bus.unsupported`.
-/
namespace Smb

class Bus (σ : Type) where
  regs : σ → Regs
  setRegs : σ → Regs → σ
  /-- One CPU read cycle. -/
  read : σ → UInt16 → UInt8 × σ
  /-- One CPU write cycle. -/
  write : σ → UInt16 → UInt8 → σ
  /-- One CPU cycle without an access (used only on the unsupported-opcode path). -/
  idle : σ → σ
  /-- Record that execution left the modelled behaviour (sticky). -/
  unsupported : σ → σ
  nmiPending : σ → Bool
  clearNmiPending : σ → σ
  /-- The NMI decision sampled by the most recent cycle's interrupt poll. -/
  nmiPolled : σ → Bool
  setNmiPolled : σ → Bool → σ

namespace CPU

variable {σ : Type} [Bus σ]

/-! ### Bus primitives

All CPU code below touches the machine state only through these. -/

@[inline] def getRegs : StateM σ Regs := fun s => (Bus.regs s, s)
@[inline] def modRegs (f : Regs → Regs) : StateM σ Unit := fun s => ((), Bus.setRegs s (f (Bus.regs s)))
@[inline] def rd (a : UInt16) : StateM σ UInt8 := fun s => Bus.read s a
@[inline] def wr (a : UInt16) (b : UInt8) : StateM σ Unit := fun s => ((), Bus.write s a b)
@[inline] def idle : StateM σ Unit := fun s => ((), Bus.idle s)
@[inline] def unsupported : StateM σ Unit := fun s => ((), Bus.unsupported s)
@[inline] def nmiPending : StateM σ Bool := fun s => (Bus.nmiPending s, s)
@[inline] def clearNmiPending : StateM σ Unit := fun s => ((), Bus.clearNmiPending s)
@[inline] def nmiPolled : StateM σ Bool := fun s => (Bus.nmiPolled s, s)
@[inline] def setNmiPolled (b : Bool) : StateM σ Unit := fun s => ((), Bus.setNmiPolled s b)

/-! ### Registers and flags -/

@[inline] def setNZ (v : UInt8) : StateM σ Unit :=
  modRegs fun r => { r with p := (r.p &&& ~~~(FN ||| FZ)) ||| (v &&& FN) ||| (if v == 0 then FZ else 0) }
@[inline] def flag (f : UInt8) : StateM σ Bool := return (← getRegs).p &&& f != 0

@[inline] def setA (v : UInt8) : StateM σ Unit := do modRegs fun r => { r with a := v }; setNZ v
@[inline] def setX (v : UInt8) : StateM σ Unit := do modRegs fun r => { r with x := v }; setNZ v
@[inline] def setY (v : UInt8) : StateM σ Unit := do modRegs fun r => { r with y := v }; setNZ v

@[inline] def fetch : StateM σ UInt8 := do
  let pc := (← getRegs).pc
  modRegs fun r => { r with pc := pc + 1 }
  rd pc

@[inline] def fetch16 : StateM σ UInt16 := do
  let lo ← fetch
  let hi ← fetch
  return lo.toUInt16 ||| (hi.toUInt16 <<< 8)

@[inline] def dummyPc : StateM σ Unit := do let _ ← rd (← getRegs).pc
@[inline] def dummyStack : StateM σ Unit := do let _ ← rd (0x100 ||| (← getRegs).s.toUInt16)

/-- A dummy read that happens only when `c` holds (indexed page crossings, forced extra
cycles of writing instructions). Its own definition so that proofs about RAM/ROM-only code
can treat it as "add one cycle if `c`" without splitting on `c`. -/
@[inline] def dummyRdIf (c : Bool) (a : UInt16) : StateM σ Unit :=
  if c then do let _ ← rd a else pure ()

@[inline] def push (v : UInt8) : StateM σ Unit := do
  let sp := (← getRegs).s
  modRegs fun r => { r with s := sp - 1 }
  wr (0x100 ||| sp.toUInt16) v

@[inline] def pull : StateM σ UInt8 := do
  let sp := (← getRegs).s
  let v ← rd (0x100 ||| (sp + 1).toUInt16)
  modRegs fun r => { r with s := sp + 1 }
  return v

/-! ### Addressing modes. `w` = the instruction writes (forces the extra indexed cycle). -/

@[inline] def aZp : StateM σ UInt16 := return (← fetch).toUInt16
@[inline] def aZpX : StateM σ UInt16 := do
  let b ← fetch; let _ ← rd b.toUInt16; return (b + (← getRegs).x).toUInt16
@[inline] def aZpY : StateM σ UInt16 := do
  let b ← fetch; let _ ← rd b.toUInt16; return (b + (← getRegs).y).toUInt16
@[inline] def aAbs : StateM σ UInt16 := fetch16
@[inline] def aAbsI (i : UInt8) (w : Bool) : StateM σ UInt16 := do
  let b ← fetch16
  let a := b + i.toUInt16
  dummyRdIf (w || (a ^^^ b) &&& 0xFF00 != 0) ((b &&& 0xFF00) ||| (a &&& 0xFF))
  return a
@[inline] def aAbsX (w : Bool) : StateM σ UInt16 := do aAbsI (← getRegs).x w
@[inline] def aAbsY (w : Bool) : StateM σ UInt16 := do aAbsI (← getRegs).y w
def aIndX : StateM σ UInt16 := do
  let z ← fetch
  let _ ← rd z.toUInt16
  let z := z + (← getRegs).x
  let lo ← rd z.toUInt16
  let hi ← rd (z + 1).toUInt16
  return lo.toUInt16 ||| (hi.toUInt16 <<< 8)
def aIndY (w : Bool) : StateM σ UInt16 := do
  let z ← fetch
  let lo ← rd z.toUInt16
  let hi ← rd (z + 1).toUInt16
  let b := lo.toUInt16 ||| (hi.toUInt16 <<< 8)
  let a := b + (← getRegs).y.toUInt16
  dummyRdIf (w || (a ^^^ b) &&& 0xFF00 != 0) ((b &&& 0xFF00) ||| (a &&& 0xFF))
  return a

/-! ### Operations -/

def adc (m : UInt8) : StateM σ Unit := do
  let r0 ← getRegs
  let sum := r0.a.toUInt16 + m.toUInt16 + (r0.p &&& FC).toUInt16
  let r := sum.toUInt8
  let p := r0.p &&& ~~~(FC ||| FV)
  let p := if sum > 0xFF then p ||| FC else p
  let p := if (~~~(r0.a ^^^ m)) &&& (r0.a ^^^ r) &&& 0x80 != 0 then p ||| FV else p
  modRegs fun regs => { regs with p, a := r }
  setNZ r

def cmp (r m : UInt8) : StateM σ Unit := do
  modRegs fun regs => { regs with p := if r ≥ m then regs.p ||| FC else regs.p &&& ~~~FC }
  setNZ (r - m)

/-- A taken branch polls interrupts early; a page-crossing one polls again. -/
def branch (cond : Bool) : StateM σ Unit := do
  let off ← fetch
  let polled ← nmiPolled
  if cond then
    dummyPc
    let pc := (← getRegs).pc
    let a := pc + off.toUInt16 + (if off &&& 0x80 != 0 then 0xFF00 else 0)
    if (a ^^^ pc) &&& 0xFF00 != 0 then
      let _ ← rd ((pc &&& 0xFF00) ||| (a &&& 0xFF))
      let now ← nmiPolled
      setNmiPolled (now || polled)
    else setNmiPolled polled
    modRegs fun r => { r with pc := a }

/-- Shift/rotate/inc/dec on `v`: 0 ASL, 1 LSR, 2 ROL, 3 ROR, 4 INC, 5 DEC. -/
def shiftOp (op : Nat) (v : UInt8) : StateM σ UInt8 := do
  let c := (← getRegs).p &&& FC
  let (r, carry) : UInt8 × Option UInt8 :=
    match op with
    | 0 => (v <<< 1, some (v >>> 7))
    | 1 => (v >>> 1, some (v &&& 1))
    | 2 => ((v <<< 1) ||| c, some (v >>> 7))
    | 3 => ((v >>> 1) ||| (c <<< 7), some (v &&& 1))
    | 4 => (v + 1, none)
    | _ => (v - 1, none)
  if let some cf := carry then modRegs fun r => { r with p := (r.p &&& ~~~FC) ||| cf }
  setNZ r
  return r

def rmw (a : UInt16) (op : Nat) : StateM σ Unit := do
  let v ← rd a
  wr a v  -- dummy write of the unmodified value
  let r ← shiftOp op v
  wr a r

/-- Push PC and P, then load the vector. An NMI arriving during BRK takes over the vector. -/
def interrupt (vec : UInt16) (brk : Bool) : StateM σ Unit := do
  let pc := (← getRegs).pc
  push (pc >>> 8).toUInt8
  push pc.toUInt8
  let pending ← nmiPending
  let vec := if pending then 0xFFFA else vec
  clearNmiPending
  push (((← getRegs).p &&& ~~~FB) ||| FU ||| (if brk then FB else 0))
  modRegs fun r => { r with p := r.p ||| FI }
  let lo ← rd vec
  let hi ← rd (vec + 1)
  modRegs fun r => { r with pc := lo.toUInt16 ||| (hi.toUInt16 <<< 8) }

def nmi : StateM σ Unit := do dummyPc; dummyPc; interrupt 0xFFFA false

@[inline] def ld (r : UInt8 → StateM σ Unit) (addr : StateM σ UInt16) : StateM σ Unit := do r (← rd (← addr))
@[inline] def st (v : Regs → UInt8) (addr : StateM σ UInt16) : StateM σ Unit := do
  let a ← addr
  wr a (v (← getRegs))

/-- Operand for the ALU group (ORA AND EOR ADC LDA CMP SBC) by the low bits of the opcode. -/
def aluOperand (op : UInt8) : StateM σ (Option UInt8) := do
  match op &&& 0x1F with
  | 0x09 => return some (← fetch)
  | 0x05 => return some (← rd (← aZp))
  | 0x15 => return some (← rd (← aZpX))
  | 0x0D => return some (← rd (← aAbs))
  | 0x1D => return some (← rd (← aAbsX false))
  | 0x19 => return some (← rd (← aAbsY false))
  | 0x01 => return some (← rd (← aIndX))
  | 0x11 => return some (← rd (← aIndY false))
  | _ => return none

def isAlu (op : UInt8) : Bool :=
  let lo := op &&& 0x1F
  op &&& 0xE0 != 0x80 &&
    (lo == 0x09 || lo == 0x05 || lo == 0x15 || lo == 0x0D || lo == 0x1D || lo == 0x19 || lo == 0x01 || lo == 0x11)

def alu (op : UInt8) : StateM σ Unit := do
  let some m ← aluOperand op | return
  let a := (← getRegs).a
  match op >>> 5 with
  | 0 => setA (a ||| m)
  | 1 => setA (a &&& m)
  | 2 => setA (a ^^^ m)
  | 3 => adc m
  | 5 => setA m
  | 6 => cmp a m
  | 7 => adc (~~~m)
  | _ => pure ()

/-- Execute the instruction with opcode `op`, whose opcode byte has been fetched. -/
def exec (op : UInt8) : StateM σ Unit :=
  if isAlu op then alu op
  else match op with
  -- loads
  | 0xA2 => do setX (← fetch)
  | 0xA6 => ld setX aZp
  | 0xB6 => ld setX aZpY
  | 0xAE => ld setX aAbs
  | 0xBE => ld setX (aAbsY false)
  | 0xA0 => do setY (← fetch)
  | 0xA4 => ld setY aZp
  | 0xB4 => ld setY aZpX
  | 0xAC => ld setY aAbs
  | 0xBC => ld setY (aAbsX false)
  -- stores
  | 0x85 => st (·.a) aZp
  | 0x95 => st (·.a) aZpX
  | 0x8D => st (·.a) aAbs
  | 0x9D => st (·.a) (aAbsX true)
  | 0x99 => st (·.a) (aAbsY true)
  | 0x81 => st (·.a) aIndX
  | 0x91 => st (·.a) (aIndY true)
  | 0x86 => st (·.x) aZp
  | 0x96 => st (·.x) aZpY
  | 0x8E => st (·.x) aAbs
  | 0x84 => st (·.y) aZp
  | 0x94 => st (·.y) aZpX
  | 0x8C => st (·.y) aAbs
  -- compares and BIT
  | 0xE0 => do let m ← fetch; cmp (← getRegs).x m
  | 0xE4 => do let m ← rd (← aZp); cmp (← getRegs).x m
  | 0xEC => do let m ← rd (← aAbs); cmp (← getRegs).x m
  | 0xC0 => do let m ← fetch; cmp (← getRegs).y m
  | 0xC4 => do let m ← rd (← aZp); cmp (← getRegs).y m
  | 0xCC => do let m ← rd (← aAbs); cmp (← getRegs).y m
  | 0x24 | 0x2C => do
    let m ← rd (← if op == 0x24 then aZp else aAbs)
    modRegs fun r => { r with p := (r.p &&& ~~~(FN ||| FV ||| FZ)) ||| (m &&& (FN ||| FV)) ||| (if r.a &&& m == 0 then FZ else 0) }
  -- read-modify-write: base 0x00 ASL, 0x40 LSR, 0x20 ROL, 0x60 ROR, 0xE0 INC, 0xC0 DEC
  | 0x06 => do rmw (← aZp) 0 | 0x16 => do rmw (← aZpX) 0 | 0x0E => do rmw (← aAbs) 0 | 0x1E => do rmw (← aAbsX true) 0
  | 0x46 => do rmw (← aZp) 1 | 0x56 => do rmw (← aZpX) 1 | 0x4E => do rmw (← aAbs) 1 | 0x5E => do rmw (← aAbsX true) 1
  | 0x26 => do rmw (← aZp) 2 | 0x36 => do rmw (← aZpX) 2 | 0x2E => do rmw (← aAbs) 2 | 0x3E => do rmw (← aAbsX true) 2
  | 0x66 => do rmw (← aZp) 3 | 0x76 => do rmw (← aZpX) 3 | 0x6E => do rmw (← aAbs) 3 | 0x7E => do rmw (← aAbsX true) 3
  | 0xE6 => do rmw (← aZp) 4 | 0xF6 => do rmw (← aZpX) 4 | 0xEE => do rmw (← aAbs) 4 | 0xFE => do rmw (← aAbsX true) 4
  | 0xC6 => do rmw (← aZp) 5 | 0xD6 => do rmw (← aZpX) 5 | 0xCE => do rmw (← aAbs) 5 | 0xDE => do rmw (← aAbsX true) 5
  | 0x0A => do dummyPc; let r ← shiftOp 0 (← getRegs).a; modRegs fun regs => { regs with a := r }
  | 0x4A => do dummyPc; let r ← shiftOp 1 (← getRegs).a; modRegs fun regs => { regs with a := r }
  | 0x2A => do dummyPc; let r ← shiftOp 2 (← getRegs).a; modRegs fun regs => { regs with a := r }
  | 0x6A => do dummyPc; let r ← shiftOp 3 (← getRegs).a; modRegs fun regs => { regs with a := r }
  | 0xE8 => do dummyPc; setX ((← getRegs).x + 1)
  | 0xCA => do dummyPc; setX ((← getRegs).x - 1)
  | 0xC8 => do dummyPc; setY ((← getRegs).y + 1)
  | 0x88 => do dummyPc; setY ((← getRegs).y - 1)
  -- transfers and flags
  | 0xAA => do dummyPc; setX (← getRegs).a
  | 0x8A => do dummyPc; setA (← getRegs).x
  | 0xA8 => do dummyPc; setY (← getRegs).a
  | 0x98 => do dummyPc; setA (← getRegs).y
  | 0xBA => do dummyPc; setX (← getRegs).s
  | 0x9A => do dummyPc; modRegs fun r => { r with s := r.x }
  | 0x18 => do dummyPc; modRegs fun r => { r with p := r.p &&& ~~~FC }
  | 0x38 => do dummyPc; modRegs fun r => { r with p := r.p ||| FC }
  | 0x58 => do dummyPc; modRegs fun r => { r with p := r.p &&& ~~~FI }
  | 0x78 => do dummyPc; modRegs fun r => { r with p := r.p ||| FI }
  | 0xB8 => do dummyPc; modRegs fun r => { r with p := r.p &&& ~~~FV }
  | 0xD8 => do dummyPc; modRegs fun r => { r with p := r.p &&& ~~~FD }
  | 0xF8 => do dummyPc; modRegs fun r => { r with p := r.p ||| FD }
  | 0xEA | 0x1A | 0x3A | 0x5A | 0x7A | 0xDA | 0xFA => dummyPc
  | 0x80 | 0x82 | 0x89 | 0xC2 | 0xE2 => do let _ ← fetch
  | 0x04 | 0x44 | 0x64 => do let _ ← rd (← aZp)
  | 0x14 | 0x34 | 0x54 | 0x74 | 0xD4 | 0xF4 => do let _ ← rd (← aZpX)
  | 0x0C => do let _ ← rd (← aAbs)
  | 0x1C | 0x3C | 0x5C | 0x7C | 0xDC | 0xFC => do let _ ← rd (← aAbsX false)
  -- stack
  | 0x48 => do dummyPc; push (← getRegs).a
  | 0x08 => do dummyPc; push ((← getRegs).p ||| FB ||| FU)
  | 0x68 => do dummyPc; dummyStack; setA (← pull)
  | 0x28 => do dummyPc; dummyStack; let v ← pull; modRegs fun r => { r with p := (v &&& ~~~FB) ||| FU }
  -- control flow
  | 0x4C => do let a ← fetch16; modRegs fun r => { r with pc := a }
  | 0x6C => do
    let ptr ← fetch16
    let lo ← rd ptr
    let hi ← rd ((ptr &&& 0xFF00) ||| ((ptr + 1) &&& 0xFF))
    modRegs fun r => { r with pc := lo.toUInt16 ||| (hi.toUInt16 <<< 8) }
  | 0x20 => do
    let lo ← fetch
    dummyStack
    let pc := (← getRegs).pc
    push (pc >>> 8).toUInt8
    push pc.toUInt8
    let hi ← fetch
    modRegs fun r => { r with pc := lo.toUInt16 ||| (hi.toUInt16 <<< 8) }
  | 0x60 => do
    dummyPc; dummyStack
    let lo ← pull
    let hi ← pull
    modRegs fun r => { r with pc := lo.toUInt16 ||| (hi.toUInt16 <<< 8) }
    dummyPc
    modRegs fun r => { r with pc := r.pc + 1 }
  | 0x40 => do
    dummyPc; dummyStack
    let v ← pull
    modRegs fun r => { r with p := (v &&& ~~~FB) ||| FU }
    let lo ← pull
    let hi ← pull
    modRegs fun r => { r with pc := lo.toUInt16 ||| (hi.toUInt16 <<< 8) }
  | 0x00 => do
    let _ ← fetch; interrupt 0xFFFE true
    setNmiPolled false
  | 0x10 => do branch (!(← flag FN))
  | 0x30 => do branch (← flag FN)
  | 0x50 => do branch (!(← flag FV))
  | 0x70 => do branch (← flag FV)
  | 0x90 => do branch (!(← flag FC))
  | 0xB0 => do branch (← flag FC)
  | 0xD0 => do branch (!(← flag FZ))
  | 0xF0 => do branch (← flag FZ)
  | _ => do unsupported; idle

/-- Everything after the opcode fetch: execute, then the interrupt checks. -/
def stepTail (op : UInt8) : StateM σ Unit := do
  exec op
  if (← getRegs).p &&& FI == 0 then unsupported  -- IRQ delivery is not modelled.
  if (← nmiPolled) then nmi

/-- Execute one instruction, then service an NMI if the last poll requested one.
(`stepTail` is everything after the opcode fetch; proofs use one lemma per opcode for it.) -/
def step : StateM σ Unit := do
  let op ← fetch
  stepTail op

end CPU
end Smb
