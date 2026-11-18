import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# `MoveObjectHorizontally` (`$BF0F`)

The routine every moving object uses to apply its horizontal speed:

```
MoveObjectHorizontally:
  lda SprObject_X_Speed,x   ; $57,x   asl×4 → $01 (low nybble moved high)
  lda SprObject_X_Speed,x   ;         lsr×4, sign-extend → $00
  ldy #0 / dey if negative  ;         → $02 (sign byte)
  lda SprObject_X_MoveForce,x ; $0400,x  += $01
  lda SprObject_X_Position,x  ; $86,x    += $00 + carry
  lda SprObject_PageLoc,x     ; $6D,x    += $02 + carry
  ...                         ; returns (carry + $00) in A
```

The *intended* summary: treat (page : position : sub-pixel force) as one 24-bit number,
and add the speed byte sign-extended and multiplied by 16. The theorem below proves this
from the ROM bytes, together with the returned `A` and `Y`, the exact cycle count and every
RAM byte the routine may change.

**What the proof attempt found.** Without a restriction on the object offset `X` the
summary is false: `bv_decide` returns a counterexample with `X = $AA`, where
`SprObject_X_Speed,x` wraps to `$01`, the scratch byte the routine has just overwritten,
so the second load of the speed reads `speed << 4` instead. Other offsets alias `$00`–`$02`
through the position and page tables (e.g. `X = $7A` makes `$86,x` wrap to `$00`).
With `X < $7A` none of the routine's addresses alias, and the summary holds. Every call in
the TAS replay has `X ≤ $15`, but that is not a proof that no input sequence reaches a larger
offset: establishing `X < $7A` at each call site is a separate, open obligation. It is the
sort of fact a hand-written movement model silently assumes.
-/
-- The linter walks the large symbolic-execution proofs for nothing.
set_option linter.unusedVariables false

namespace Smb.Routine

/-- `$BF0F`–`$BF4C`, including the final RTS. -/
def moveObjectHorizontallyCode : List UInt8 :=
  smbPrg% 0xBF0F 62

/-- Run from the routine's entry to its RTS (exclusive). Every path takes at most 38
instructions; the fuel is only an upper bound. -/
def moveObjectHorizontallyRun (s : Plain) : Plain :=
  ((CPU.runTo (σ := Plain) 0xBF4C 40).run s).2

/-- The RAM indices the routine uses for object `x`, in the form the CPU computes them. -/
def speedIdx (x : UInt8) : UInt16 := (0x57 + x).toUInt16 &&& 0x7FF
def forceIdx (x : UInt8) : UInt16 := (0x400 + x.toUInt16) &&& 0x7FF
def posIdx (x : UInt8) : UInt16 := (0x86 + x).toUInt16 &&& 0x7FF
def pageIdx (x : UInt8) : UInt16 := (0x6D + x).toUInt16 &&& 0x7FF

/-- Page, position and sub-pixel force as one 24-bit quantity (in a `UInt32`). -/
def pos24 (ram : UInt16 → UInt8) (x : UInt8) : UInt32 :=
  ((ram (pageIdx x)).toUInt32 <<< 16) ||| ((ram (posIdx x)).toUInt32 <<< 8) ||| (ram (forceIdx x)).toUInt32

/-- The speed byte sign-extended to 32 bits. -/
def sext (v : UInt8) : UInt32 := if v ≥ 0x80 then v.toUInt32 ||| 0xFFFFFF00 else v.toUInt32

/-- The summary of one call, for object offset `x`, stack pointer `sp`, and the RAM and
cycle count on entry. Callers use the returned `A`, the whole-pixel movement (mod 256):
`MovePlayerHorizontally` stores it in `Player_X_Scroll`, and `MoveEnemyHorizontally` passes
it on. The flags are not summarized; the direct callers set them again before testing them. -/
def Summary (x sp : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64) (s : Plain) : Prop :=
  let v := ram (speedIdx x)
  s.bad = false ∧ s.regs.pc = 0xBF4C ∧ s.regs.x = x ∧ s.regs.s = sp ∧
  s.regs.a = s.ram (posIdx x) - ram (posIdx x) ∧ s.regs.y = (if v ≥ 0x80 then 0xFF else 0) ∧
  pos24 s.ram x = (pos24 ram x + sext v * 16) &&& 0xFFFFFF ∧
  s.cyc = cyc + (if v ≥ 0x80 then 101 else 99) ∧
  (∀ i : UInt16, i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ forceIdx x → i ≠ posIdx x → i ≠ pageIdx x →
    i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF → s.ram i = ram i)

set_option maxHeartbeats 20000000 in
theorem moveObjectHorizontally
    (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x3F0F moveObjectHorizontallyCode) (hp : p &&& 4 ≠ 0) (hx : x < 0x7A) :
    Summary x sp ram cyc (moveObjectHorizontallyRun ⟨⟨0xBF0F, a, x, y, sp, p⟩, ram, prg, cyc, false⟩) := by
  simp only [CodeAt, moveObjectHorizontallyCode, UInt16.reduceAdd] at hcode
  generalize hrun : moveObjectHorizontallyRun ⟨⟨0xBF0F, a, x, y, sp, p⟩, ram, prg, cyc, false⟩ = f
  unfold moveObjectHorizontallyRun at hrun
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hrun [hcode, hI]
  all_goals
    intros
    clear hcode hI
    simp only [Summary, pos24, sext, speedIdx, forceIdx, posIdx, pageIdx, bne] at *
    -- One `bv_decide` for all register/position/cycle claims, one for the RAM frame.
    simp only [← and_assoc]
    refine ⟨?_, fun i h0 h1 h2 h3 h4 h5 h6 => ?_⟩ <;> bv_decide

end Smb.Routine
