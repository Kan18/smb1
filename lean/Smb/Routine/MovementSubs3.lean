import Smb.Summary
import Smb.Routine.GroundFrame
import Smb.Routine.Climbing

/-! `PlayerMovementSubs` while climbing (`Player_State = 3`): `PlayerPhysicsSub`'s climb branch and `ClimbingSub`, run inline. See
`Smb.Routine.MovementSubs`. Only `$070B = 0` is needed besides the state. -/
namespace Smb.Routine
set_option linter.unusedVariables false

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem ms3_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xB329 ≤ a && a ≤ 0xC046) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x3329 movementSubsCode) (hecode : CodeAt prg 0x0E04 jumpEngineCode)
    (hpcode : CodeAt prg 0x3424 physicsCode) (hccode : CodeAt prg 0x33C7 climbingCode)
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 3) (hsize : ram 0x70B = 0) :
    ((CPU.runTo (σ := Plain) stop (m + 200)).run ⟨⟨0xB329, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, movementSubsCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, jumpEngineCode, UInt16.reduceAdd] at hecode
  simp only [CodeAt, physicsCode, UInt16.reduceAdd] at hpcode
  simp only [CodeAt, climbingCode, UInt16.reduceAdd] at hccode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 200)).run ⟨⟨0xB329, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary ms3 hrun [hcode, hecode, hpcode, hccode, hI, hst, hsize] until [46111, 46115]
    exact finish (clear hcode hecode hpcode hccode; exact_finish ms3)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface ms3
summary_regs ms3

end Smb.Routine
