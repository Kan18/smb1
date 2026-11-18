import Smb.Data.ProofRom
import Smb.Routine.PhysicsCall
import Smb.Routine.OnGround
import Smb.Routine.JumpSwimSub

/-!
# A frame of Mario's movement from the ground (`PlayerMovementSubs`, `$B329`)

```
PlayerMovementSubs:  crouch flag; jsr PlayerPhysicsSub (jump start, X physics)
                     unless growing/shrinking: jsr JumpEngine on Player_State
                       0 → OnGroundStateSub   1 → JumpSwimSub   2 → FallingSub   3 → ClimbingSub
```

From the ground (`Player_State = 0`), the dispatch uses the state *after* the jump check, so
the frame a jump starts is already a `JumpSwimSub` frame: the position update uses the fresh jump
speed, so Mario already rises 4 or 5 pixels (exact output in `FreshJump`), and the velocity becomes
`gravityVel` of the table speed with the jump gravity. Proved through call theorems of every callee (`PlayerPhysicsSub`,
`GetPlayerAnimSpeed`, `ImposeFriction`, `MovePlayerHorizontally`, `MovePlayerVertically`);
`JumpEngine`'s indirect jump is split on whether the jump started. Without a jump, Mario's
vertical state (speed, force, sub-pixel, position) is left as it was.
-/
namespace Smb.Routine

/-- `$B329`–`$B3C6`: `PlayerMovementSubs`, its `JumpEngine` table, `OnGroundStateSub`,
`FallingSub`, `JumpSwimSub`. -/
def movementSubsCode : List UInt8 :=
  smbPrg% 0xB329 158

/-- `$8E04`–`$8E18`: `JumpEngine`. -/
def jumpEngineCode : List UInt8 :=
  smbPrg% 0x8E04 21

def GroundFrameSummary (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  let c := jumpClass (ram 0x704) (ram 0x47D) (ram 0x700)
  t.bad = false ∧
  (startsJump ram = true →
    t.regs.pc = 0xC046 ∧ t.ram 0x1D = 1 ∧ t.ram 0x416 = 0 ∧
    yvel16 t.ram 0 = gravityVel 0 (bif ram 0x0E == 0x0B then 0x28 else jumpMForce c) 0 4
      ((jumpYSpeed c).toUInt16 <<< 8)) ∧
  (startsJump ram = false → t.regs.pc = 0xB36C ∧ t.ram 0x1D = 0 ∧ t.ram 0x9F = ram 0x9F ∧
    t.ram 0x433 = ram 0x433 ∧ t.ram 0x416 = ram 0x416 ∧ t.ram 0xCE = ram 0xCE ∧ t.ram 0xB5 = ram 0xB5)

set_option linter.unusedVariables false


theorem startsJump_stack_keep (ram : UInt16 → UInt8) (sp v : UInt8) :
    startsJump (fun i => bif i == ((0x100 ||| sp.toUInt16) &&& 0x7FF) then v else ram i) = startsJump ram := by
  simp only [startsJump, bne]
  bv_decide

theorem startsJump_crouch_keep (ram : UInt16 → UInt8) (v : UInt8) :
    startsJump (fun i => bif i == 0x714 then v else ram i) = startsJump ram := by
  simp [startsJump]



end Smb.Routine
