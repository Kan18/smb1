import Smb.Cpu

/-!
# A bare 6502 machine for routine-level proofs

2 KB of RAM (mirrored below `$2000`) and 32 KB of ROM at `$8000`, as plain functions so
that symbolic execution yields bitvector terms. Every bus access takes one cycle. An access
anywhere else, an unsupported opcode, or clearing the I flag sets the sticky `bad` flag
(as a value, without branching): such executions are outside this machine and theorems
about it say nothing about them.

There are no interrupts. `Smb.Refine` shows that, while NMI generation is off and no DMA
is pending, the full NES changes its CPU registers, RAM and cycle count exactly as this
machine does whenever this machine's run is not `bad`.
-/
namespace Smb

structure Plain where
  regs : Regs
  /-- RAM, indexed by `address &&& 0x7FF`. -/
  ram : UInt16 → UInt8
  /-- ROM, indexed by `address &&& 0x7FFF`. -/
  prg : UInt16 → UInt8
  cyc : UInt64
  bad : Bool

namespace Plain

/-! Bus accesses never branch on the address. An access outside RAM/ROM (or a write outside
RAM) only sets `bad`, so symbolic execution needs no case analysis on addresses: whether an
access was in range becomes part of the final `bad = false` obligation. -/

def inRam (a : UInt16) : Bool := a < 0x2000
def readable (a : UInt16) : Bool := a < 0x2000 || 0x8000 ≤ a
def memRead (ram prg : UInt16 → UInt8) (a : UInt16) : UInt8 :=
  bif inRam a then ram (a &&& 0x7FF) else prg (a &&& 0x7FFF)

def read (s : Plain) (a : UInt16) : UInt8 × Plain :=
  (memRead s.ram s.prg a, { s with cyc := s.cyc + 1, bad := s.bad || !readable a })

def write (s : Plain) (a : UInt16) (b : UInt8) : Plain :=
  { s with cyc := s.cyc + 1, ram := fun i => bif inRam a && i == a &&& 0x7FF then b else s.ram i,
           bad := s.bad || !inRam a }

instance : Bus Plain where
  regs s := s.regs
  setRegs s r := { s with regs := r }
  read := read
  write := write
  idle s := { s with cyc := s.cyc + 1 }
  unsupported s := { s with bad := true }
  nmiPending _ := false
  clearNmiPending s := s
  nmiPolled _ := false
  setNmiPolled s _ := s

/-- Run `n` instructions. -/
def run : Nat → Plain → Plain
  | 0, s => s
  | n + 1, s => run n (CPU.step.run s).2

end Plain
end Smb
