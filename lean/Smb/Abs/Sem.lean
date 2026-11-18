import Smb.Regs

/-!
# One 6502 instruction as a pure function of the values it reads

`Smb.Abs.eval` gives an instruction's result from its opcode and operand bytes, the registers, and the
memory values it reads, passed as arguments (`lo`, `hi`: a pointer or pulled address; `v`: the data operand).
It uses no memory, so a checker can run it on every combination of values a state description allows.
It covers the 110 opcodes the game's code uses. `Smb.Routine.AbsSem` proves it agrees with `CPU.step`.
-/
namespace Smb.Abs
open CPU

inductive Mode where
  | imm | zp | zpx | zpy | abs | absx | absy | indx | indy
  deriving DecidableEq, Repr, Inhabited

inductive Reg where
  | a | x | y
  deriving DecidableEq, Repr, Inhabited

/-- The instruction classes; the ALU and shift operations are numbered as in `CPU.alu` and `CPU.shiftOp`. -/
inductive Kind where
  | alu (k : Nat) (m : Mode)
  | load (r : Reg) (m : Mode)
  | store (r : Reg) (m : Mode)
  | cmp (r : Reg) (m : Mode)
  | bit (m : Mode)
  | rmw (k : Nat) (m : Mode)
  | shiftA (k : Nat)
  | incdec (r : Reg) (d : UInt8)
  | xfer (src dst : Reg)
  | setp (clear set : UInt8)
  | branch (mask : UInt8) (want : Bool)
  | jmp | jmpi | jsr | rts | rti | pha | pla | txs
  | unknown
  deriving DecidableEq, Repr, Inhabited

def decode (op : UInt8) : Kind :=
  match op.toNat with
  | 0xA9 => .load .a .imm | 0xA5 => .load .a .zp | 0xB5 => .load .a .zpx | 0xAD => .load .a .abs
  | 0xBD => .load .a .absx | 0xB9 => .load .a .absy | 0xB1 => .load .a .indy
  | 0xA2 => .load .x .imm | 0xA6 => .load .x .zp | 0xB6 => .load .x .zpy | 0xAE => .load .x .abs | 0xBE => .load .x .absy
  | 0xA0 => .load .y .imm | 0xA4 => .load .y .zp | 0xB4 => .load .y .zpx | 0xAC => .load .y .abs | 0xBC => .load .y .absx
  | 0x85 => .store .a .zp | 0x95 => .store .a .zpx | 0x8D => .store .a .abs | 0x9D => .store .a .absx
  | 0x99 => .store .a .absy | 0x91 => .store .a .indy
  | 0x86 => .store .x .zp | 0x8E => .store .x .abs
  | 0x84 => .store .y .zp | 0x94 => .store .y .zpx | 0x8C => .store .y .abs
  | 0x09 => .alu 0 .imm | 0x05 => .alu 0 .zp | 0x15 => .alu 0 .zpx | 0x0D => .alu 0 .abs | 0x1D => .alu 0 .absx | 0x19 => .alu 0 .absy
  | 0x29 => .alu 1 .imm | 0x25 => .alu 1 .zp | 0x2D => .alu 1 .abs | 0x3D => .alu 1 .absx | 0x39 => .alu 1 .absy
  | 0x49 => .alu 2 .imm | 0x45 => .alu 2 .zp
  | 0x69 => .alu 3 .imm | 0x65 => .alu 3 .zp | 0x75 => .alu 3 .zpx | 0x6D => .alu 3 .abs | 0x7D => .alu 3 .absx | 0x79 => .alu 3 .absy
  | 0xC9 => .alu 6 .imm | 0xC5 => .alu 6 .zp | 0xD5 => .alu 6 .zpx | 0xCD => .alu 6 .abs | 0xDD => .alu 6 .absx | 0xD9 => .alu 6 .absy
  | 0xE9 => .alu 7 .imm | 0xE5 => .alu 7 .zp | 0xF5 => .alu 7 .zpx | 0xED => .alu 7 .abs | 0xFD => .alu 7 .absx | 0xF9 => .alu 7 .absy
  | 0xE0 => .cmp .x .imm | 0xE4 => .cmp .x .zp
  | 0xC0 => .cmp .y .imm | 0xC4 => .cmp .y .zp | 0xCC => .cmp .y .abs
  | 0x24 => .bit .zp | 0x2C => .bit .abs
  | 0x0E => .rmw 0 .abs
  | 0x46 => .rmw 1 .zp | 0x4E => .rmw 1 .abs
  | 0x26 => .rmw 2 .zp | 0x2E => .rmw 2 .abs
  | 0x7E => .rmw 3 .absx
  | 0xE6 => .rmw 4 .zp | 0xF6 => .rmw 4 .zpx | 0xEE => .rmw 4 .abs | 0xFE => .rmw 4 .absx
  | 0xC6 => .rmw 5 .zp | 0xD6 => .rmw 5 .zpx | 0xCE => .rmw 5 .abs | 0xDE => .rmw 5 .absx
  | 0x0A => .shiftA 0 | 0x4A => .shiftA 1 | 0x2A => .shiftA 2 | 0x6A => .shiftA 3
  | 0xE8 => .incdec .x 1 | 0xCA => .incdec .x 0xFF | 0xC8 => .incdec .y 1 | 0x88 => .incdec .y 0xFF
  | 0xAA => .xfer .a .x | 0x8A => .xfer .x .a | 0xA8 => .xfer .a .y | 0x98 => .xfer .y .a
  | 0x9A => .txs
  | 0x18 => .setp 1 0 | 0x38 => .setp 0 1 | 0x78 => .setp 0 4 | 0xD8 => .setp 8 0
  | 0x10 => .branch 0x80 false | 0x30 => .branch 0x80 true
  | 0x90 => .branch 1 false | 0xB0 => .branch 1 true
  | 0xD0 => .branch 2 false | 0xF0 => .branch 2 true
  | 0x4C => .jmp | 0x6C => .jmpi | 0x20 => .jsr | 0x60 => .rts | 0x40 => .rti
  | 0x48 => .pha | 0x68 => .pla
  | _ => .unknown

@[inline] def base (lo hi : UInt8) : UInt16 := lo.toUInt16 ||| hi.toUInt16 <<< 8

/-- `P` with N and Z set from `v`. -/
@[inline] def nz (p v : UInt8) : UInt8 :=
  (p &&& ~~~(FN ||| FZ)) ||| (v &&& FN) ||| (if v == 0 then FZ else 0)

/-- Bytes of an instruction in this mode, opcode included. -/
def Mode.size : Mode → UInt16
  | .imm | .zp | .zpx | .zpy | .indx | .indy => 2
  | .abs | .absx | .absy => 3

/-- The zero-page cells holding an indirect mode's pointer. -/
def ptrCells (m : Mode) (b1 x : UInt8) : UInt16 × UInt16 :=
  match m with
  | .indy => (b1.toUInt16, (b1 + 1).toUInt16)
  | .indx => ((b1 + x).toUInt16, (b1 + x + 1).toUInt16)
  | _ => (0, 0)

/-- The address a mode accesses (for `.imm`, nothing is read). -/
def ea (m : Mode) (b1 b2 x y lo hi : UInt8) : UInt16 :=
  match m with
  | .imm => 0
  | .zp => b1.toUInt16
  | .zpx => (b1 + x).toUInt16
  | .zpy => (b1 + y).toUInt16
  | .abs => base b1 b2
  | .absx => base b1 b2 + x.toUInt16
  | .absy => base b1 b2 + y.toUInt16
  | .indx => base lo hi
  | .indy => base lo hi + y.toUInt16

def regOf (r : Reg) (a x y : UInt8) : UInt8 :=
  match r with | .a => a | .x => x | .y => y

/-- `(new A, new P)` for an ALU operation on operand `m`. -/
def aluFn (k : Nat) (a m p : UInt8) : UInt8 × UInt8 :=
  let addc (m : UInt8) : UInt8 × UInt8 :=
    let sum := a.toUInt16 + m.toUInt16 + (p &&& FC).toUInt16
    let r := sum.toUInt8
    let p1 := p &&& ~~~(FC ||| FV)
    let p2 := if sum > 0xFF then p1 ||| FC else p1
    let p3 := if (~~~(a ^^^ m)) &&& (a ^^^ r) &&& 0x80 != 0 then p2 ||| FV else p2
    (r, nz p3 r)
  match k with
  | 0 => (a ||| m, nz p (a ||| m))
  | 1 => (a &&& m, nz p (a &&& m))
  | 2 => (a ^^^ m, nz p (a ^^^ m))
  | 3 => addc m
  | 6 => (a, nz (if a ≥ m then p ||| FC else p &&& ~~~FC) (a - m))
  | _ => addc (~~~m)

/-- `(result, new P)` for a shift, rotate, increment or decrement. -/
def shiftFn (k : Nat) (v p : UInt8) : UInt8 × UInt8 :=
  let c := p &&& FC
  let withC (cf : UInt8) := (p &&& ~~~FC) ||| cf
  match k with
  | 0 => (v <<< 1, nz (withC (v >>> 7)) (v <<< 1))
  | 1 => (v >>> 1, nz (withC (v &&& 1)) (v >>> 1))
  | 2 => ((v <<< 1) ||| c, nz (withC (v >>> 7)) ((v <<< 1) ||| c))
  | 3 => ((v >>> 1) ||| (c <<< 7), nz (withC (v &&& 1)) ((v >>> 1) ||| (c <<< 7)))
  | 4 => (v + 1, nz p (v + 1))
  | _ => (v - 1, nz p (v - 1))

def relTarget (pc : UInt16) (off : UInt8) : UInt16 :=
  pc + 2 + off.toUInt16 + (bif off &&& 128 != 0 then 65280 else 0)

/-- The result of an instruction: registers, and RAM writes in order (the last to an address wins). -/
structure Eff where
  regs : Regs
  wr : List (UInt16 × UInt8)
  deriving Inhabited

def stack (s : UInt8) : UInt16 := 0x100 ||| s.toUInt16

def eval (k : Kind) (b1 b2 : UInt8) (r : Regs) (lo hi v : UInt8) : Eff :=
  let ⟨pc, a, x, y, s, p⟩ := r
  match k with
  | .alu k m =>
    let w := if m = .imm then b1 else v
    let (a', p') := aluFn k a w p
    ⟨⟨pc + m.size, a', x, y, s, p'⟩, []⟩
  | .load .a m => let w := if m = .imm then b1 else v; ⟨⟨pc + m.size, w, x, y, s, nz p w⟩, []⟩
  | .load .x m => let w := if m = .imm then b1 else v; ⟨⟨pc + m.size, a, w, y, s, nz p w⟩, []⟩
  | .load .y m => let w := if m = .imm then b1 else v; ⟨⟨pc + m.size, a, x, w, s, nz p w⟩, []⟩
  | .store rg m => ⟨⟨pc + m.size, a, x, y, s, p⟩, [(ea m b1 b2 x y lo hi, regOf rg a x y)]⟩
  | .cmp rg m =>
    let w := if m = .imm then b1 else v
    let c := regOf rg a x y
    ⟨⟨pc + m.size, a, x, y, s, nz (if c ≥ w then p ||| FC else p &&& ~~~FC) (c - w)⟩, []⟩
  | .bit m =>
    ⟨⟨pc + m.size, a, x, y, s, (p &&& ~~~(FN ||| FV ||| FZ)) ||| (v &&& (FN ||| FV)) ||| (if a &&& v == 0 then FZ else 0)⟩, []⟩
  | .rmw k m =>
    let (w, p') := shiftFn k v p
    ⟨⟨pc + m.size, a, x, y, s, p'⟩, [(ea m b1 b2 x y lo hi, w)]⟩
  | .shiftA k => let (w, p') := shiftFn k a p; ⟨⟨pc + 1, w, x, y, s, p'⟩, []⟩
  | .incdec .x d => ⟨⟨pc + 1, a, x + d, y, s, nz p (x + d)⟩, []⟩
  | .incdec .y d => ⟨⟨pc + 1, a, x, y + d, s, nz p (y + d)⟩, []⟩
  | .incdec .a _ => ⟨r, []⟩
  | .xfer src .a => let w := regOf src a x y; ⟨⟨pc + 1, w, x, y, s, nz p w⟩, []⟩
  | .xfer src .x => let w := regOf src a x y; ⟨⟨pc + 1, a, w, y, s, nz p w⟩, []⟩
  | .xfer src .y => let w := regOf src a x y; ⟨⟨pc + 1, a, x, w, s, nz p w⟩, []⟩
  | .setp c st => ⟨⟨pc + 1, a, x, y, s, (p &&& ~~~c) ||| st⟩, []⟩
  | .branch mask want =>
    let taken := (p &&& mask != 0) == want
    ⟨⟨if taken then relTarget pc b1 else pc + 2, a, x, y, s, p⟩, []⟩
  | .jmp => ⟨⟨base b1 b2, a, x, y, s, p⟩, []⟩
  | .jmpi => ⟨⟨base lo hi, a, x, y, s, p⟩, []⟩
  | .jsr =>
    let ret := pc + 2
    ⟨⟨base b1 b2, a, x, y, s - 2, p⟩, [(stack s, (ret >>> 8).toUInt8), (stack (s - 1), ret.toUInt8)]⟩
  | .rts => ⟨⟨base lo hi + 1, a, x, y, s + 2, p⟩, []⟩
  | .rti => ⟨⟨base lo hi, a, x, y, s + 3, (v &&& ~~~FB) ||| FU⟩, []⟩
  | .pha => ⟨⟨pc + 1, a, x, y, s - 1, p⟩, [(stack s, a)]⟩
  | .pla => ⟨⟨pc + 1, v, x, y, s + 1, nz p v⟩, []⟩
  | .txs => ⟨⟨pc + 1, a, x, y, x, p⟩, []⟩
  | .unknown => ⟨r, []⟩

/-- Addresses of the two pointer reads. `jmpi` reads through its operand with the page-wrap bug. -/
def ptrAddrs (k : Kind) (b1 b2 : UInt8) (r : Regs) : UInt16 × UInt16 :=
  match k with
  | .alu _ m | .load _ m | .store _ m | .cmp _ m | .bit m | .rmw _ m => ptrCells m b1 r.x
  | .jmpi =>
    let p := base b1 b2
    (p, (p &&& 0xFF00) ||| ((p + 1) &&& 0xFF))
  | .rts => (stack (r.s + 1), stack (r.s + 2))
  | .rti => (stack (r.s + 2), stack (r.s + 3))
  | _ => (0, 0)

/-- Address of the data operand, when there is one. -/
def operandAddr (k : Kind) (b1 b2 : UInt8) (r : Regs) (lo hi : UInt8) : UInt16 :=
  match k with
  | .alu _ m | .load _ m | .cmp _ m | .bit m | .rmw _ m | .store _ m => ea m b1 b2 r.x r.y lo hi
  | .rti | .pla => stack (r.s + 1)
  | _ => 0

/-- Whether the instruction's accesses stay in RAM and ROM on the plain machine, its writes in RAM. -/
def accessOk (k : Kind) (b1 b2 : UInt8) (r : Regs) (lo hi : UInt8) : Bool :=
  let inR (a : UInt16) := a < 0x2000
  let rdOk (a : UInt16) := a < 0x2000 || 0x8000 ≤ a
  -- an indexed access stays on one side, its dummy read included
  let idx (b : UInt16) :=
    (b ≤ 0x1F00) || 0x8000 ≤ b
  let modeOk (m : Mode) :=
    match m with
    | .imm | .zp | .zpx | .zpy | .indx => true
    | .abs => rdOk (base b1 b2)
    | .absx => idx (base b1 b2)
    | .absy => idx (base b1 b2)
    | .indy => idx (base lo hi)
  match k with
  | .alu _ m | .load _ m | .cmp _ m | .bit m => modeOk m
  | .store _ m | .rmw _ m => modeOk m && inR (ea m b1 b2 r.x r.y lo hi)
  | .jmp | .jsr => 0x8000 ≤ base b1 b2 && base b1 b2 ≤ 0xFFF0
  | .jmpi => (base b1 b2 ≤ 0x1F00) && 0x8000 ≤ base lo hi && base lo hi ≤ 0xFFF0
  | .rts => 0x8000 ≤ base lo hi && base lo hi ≤ 0xFFEF
  | .rti => 0x8000 ≤ base lo hi && base lo hi ≤ 0xFFF0
  | .branch _ _ =>
    let t := relTarget r.pc b1
    0x8000 ≤ t && t ≤ 0xFFF0
  | .unknown => false
  | _ => true

end Smb.Abs
