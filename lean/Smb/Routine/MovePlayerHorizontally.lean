import Smb.Data.ProofRom
import Smb.Routine.MoveObjectHorizontally

/-!
# `MovePlayerHorizontally` (`$BF09`) as a call theorem

```
MovePlayerHorizontally:  lda JumpspringAnimCtrl; bne ExXMove (the RTS at $BF4C); tax
                         (falls into MoveObjectHorizontally with X = 0)
```

Closed form at the RTS: unless a jumpspring is animating, Mario's 24-bit horizontal position
(`Player_PageLoc : Player_X_Position : Player_X_MoveForce`) gains `16 × sign_extend(speed)`, and
`A` returns the whole-pixel movement (the caller stores it in `Player_X_Scroll`).
-/
namespace Smb.Routine

/-- `$BF09`–`$BF4C`: the three-instruction prefix and `MoveObjectHorizontally` (with its RTS). -/
def movePlayerHorizontallyCode : List UInt8 := smbPrg% 0xBF09 6 ++
  moveObjectHorizontallyCode

/-- Mario's new 24-bit position. -/
def mphPos (ram : UInt16 → UInt8) : UInt32 := (pos24 ram 0 + sext (ram 0x57) * 16) &&& 0xFFFFFF

/-- The low nybble of the speed moved high (`$01`), and the high nybble sign-extended (`$00`). -/
def mphLo (v : UInt8) : UInt8 := v <<< 4
def mphHi (v : UInt8) : UInt8 := bif v >>> 4 < 8 then v >>> 4 else (v >>> 4) ||| 0xF0

/-- The carry out of the sub-pixel addition (pushed on the stack). -/
def mphCarry (ram : UInt16 → UInt8) : UInt8 :=
  bif (ram 0x400).toUInt16 + (mphLo (ram 0x57)).toUInt16 > 0xFF then 1 else 0

def mphRam (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  let mv := ram 0x70E == 0
  bif mv && i == 0x400 then (mphPos ram).toUInt8
  else bif mv && i == 0x86 then (mphPos ram >>> 8).toUInt8
  else bif mv && i == 0x6D then (mphPos ram >>> 16).toUInt8
  else bif mv && i == 0 then mphHi (ram 0x57)
  else bif mv && i == 1 then mphLo (ram 0x57)
  else bif mv && i == 2 then (bif ram 0x57 ≥ 0x80 then 0xFF else 0)
  else bif mv && i == (0x100 ||| sp.toUInt16) &&& 0x7FF then mphCarry ram
  else ram i

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem movePlayerHorizontally_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xBF09 ≤ a && a ≤ 0xBF4C) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 50)).run ⟨⟨0xBF09, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xBF4C,
        bif ram 0x70E == 0 then mphCarry ram + mphHi (ram 0x57) else ram 0x70E,
        bif ram 0x70E == 0 then 0 else x,
        bif ram 0x70E == 0 then (bif ram 0x57 ≥ 0x80 then 0xFF else 0) else y, sp, p'⟩,
        mphRam sp ram, prg,
        cyc + (bif ram 0x70E == 0 then (bif ram 0x57 ≥ 0x80 then 109 else 107) else 7), bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, movePlayerHorizontallyCode, moveObjectHorizontallyCode, List.cons_append,
    List.nil_append, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 50)).run ⟨⟨0xBF09, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI] until 48972
  all_goals
    intros
    clear hcode
    subst hrun
    call_finish [mphRam, mphPos, mphLo, mphHi, mphCarry, pos24, sext, pageIdx, posIdx, forceIdx, speedIdx]

end Smb.Routine
