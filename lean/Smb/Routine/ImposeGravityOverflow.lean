import Smb.Routine.ImposeGravity

/-!
# `ImposeGravity` outside the no-overflow range

Speed `$80` (−128) with maximum 4: `speed - max = $7C` has its sign bit clear, so the routine
treats the object as falling at or above the maximum and clamps it to speed 4, fraction 0.
The intended (signed) update would leave it rising at about −128 + gravity.
-/
-- The linter walks the large symbolic-execution proofs for nothing.
set_option linter.unusedVariables false

namespace Smb.Routine

/-- Object 0 rising at speed `$80`, fraction `$80`; gravity `$50`, maximum 4. -/
def overflowRam : UInt16 → UInt8 := fun i =>
  if i = 0 then 0x50 else if i = 2 then 4 else
  if i = ySpeedIdx 0 then 0x80 else if i = yForceIdx 0 then 0x80 else 0

set_option maxHeartbeats 20000000 in
theorem imposeGravity_overflow (y sp p : UInt8) (prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x3FD7 imposeGravityCode) (hp : p &&& 4 ≠ 0) :
    -- The intended update keeps it rising ...
    gravityVel 0 0x50 0 4 0x8080 = 0x80D0 ∧
    -- ... but the routine sets speed 4, fraction 0.
    yvel16 (imposeGravityRun ⟨⟨0xBFD7, 0, 0, y, sp, p⟩, overflowRam, prg, cyc, false⟩).ram 0 = 0x0400 := by
  refine ⟨by decide, ?_⟩
  simp only [CodeAt, imposeGravityCode, UInt16.reduceAdd] at hcode
  generalize hrun : imposeGravityRun ⟨⟨0xBFD7, 0, 0, y, sp, p⟩, overflowRam, prg, cyc, false⟩ = f
  unfold imposeGravityRun at hrun
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hrun [hcode, hI, overflowRam, ySpeedIdx, yForceIdx]
  all_goals
    intros
    clear hcode hI
    simp only [yvel16, ySpeedIdx, yForceIdx] at *
    bv_decide (config := { enums := false })

end Smb.Routine
