import Smb.Routine.MoveObjectHorizontally

/-!
# Why `moveObjectHorizontally` needs `X < $7A`

The precondition is not a proof convenience. With `X = $AA`, `SprObject_X_Speed,x` is `$01`,
the scratch byte the routine overwrites with `speed << 4` before loading the speed a second
time. A speed of `$10` (one pixel per frame) then moves the object by nothing: the second
load sees `$00` and the high nybble added to the position is 0.

(Found by `bv_decide` as a counterexample to the summary without the precondition.)
-/
-- The linter walks the large symbolic-execution proofs for nothing.
set_option linter.unusedVariables false

namespace Smb.Routine

/-- RAM with `$10` at `$01` (the speed byte of object offset `$AA`) and zero elsewhere. -/
def aliasRam : UInt16 → UInt8 := fun i => if i = 1 then 0x10 else 0

set_option maxHeartbeats 20000000 in
theorem moveObjectHorizontally_alias (a y sp p : UInt8) (prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x3F0F moveObjectHorizontallyCode) (hp : p &&& 4 ≠ 0) :
    -- The speed byte is 0x10 (one pixel per frame) ...
    aliasRam (speedIdx 0xAA) = 0x10 ∧
    -- ... but page, position and sub-pixel force are unchanged.
    pos24 (moveObjectHorizontallyRun ⟨⟨0xBF0F, a, 0xAA, y, sp, p⟩, aliasRam, prg, cyc, false⟩).ram 0xAA =
      pos24 aliasRam 0xAA := by
  simp only [CodeAt, moveObjectHorizontallyCode, UInt16.reduceAdd] at hcode
  generalize hrun : moveObjectHorizontallyRun ⟨⟨0xBF0F, a, 0xAA, y, sp, p⟩, aliasRam, prg, cyc, false⟩ = f
  unfold moveObjectHorizontallyRun at hrun
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hrun [hcode, hI, aliasRam]
  all_goals
    intros
    clear hcode hI
    simp only [pos24, speedIdx, forceIdx, posIdx, pageIdx, aliasRam] at *
    constructor <;> bv_decide (config := { enums := false })

end Smb.Routine
