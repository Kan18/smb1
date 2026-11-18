import Smb.Data.ProofRom
import Smb.Routine.ImposeFriction
import Smb.Routine.MovePlayerHorizontally
import Smb.Routine.MovePlayerVertically

/-!
# `JumpSwimSub` (`$B376`): Mario in the air, one frame

```
JumpSwimSub:  if Y_Speed ≥ 0, or (A not held this and last frame and JumpOrigin_Y − Y ≥ DiffToHaltJump):
                VerticalForce := VerticalForceDown              (switch to falling gravity)
              (swimming: animation and surface handling — excluded here)
LRAir:        if left/right held: ImposeFriction                (no input: horizontal speed kept)
JSMove:       MovePlayerHorizontally; Player_X_Scroll := A
              if GameEngineSubroutine = $0B: VerticalForce := $28
              jmp MovePlayerVertically                          (gravity VerticalForce, max 4)
```

The theorem runs it through the call theorems of its three callees: one path per branch of
`JumpSwimSub` itself. Consequences for movement models: the vertical position moves by the
velocity from *before* this frame's gravity, the horizontal position by the speed *after*
this frame's friction, and with no left/right input the horizontal speed does not change in
the air.
-/
namespace Smb.Routine

/-- `$B376`–`$B3C6`. -/
def jumpSwimCode : List UInt8 :=
  smbPrg% 0xB376 81

/-- The gravity used this frame. -/
def jssForce (ram : UInt16 → UInt8) : UInt8 :=
  let fall := ram 0x9F < 0x80 ||
    (ram 0x0A &&& 0x80 &&& ram 0x0D == 0 && ram 0x708 - ram 0xCE ≥ ram 0x706)
  bif ram 0x0E == 0x0B then 0x28 else bif fall then ram 0x70A else ram 0x709

def JumpSwimSummary (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xC046 ∧ t.bad = false ∧
  t.ram 0x709 = jssForce ram ∧
  yvel16 t.ram 0 = gravityVel 0 (jssForce ram) 0 4 (yvel16 ram 0) ∧
  ypos24 t.ram 0 = (ypos24 ram 0 + sext16 (yvel16 ram 0)) &&& 0xFFFFFF ∧
  t.ram 0x57 = (bif ram 0x0C == 0 then ram 0x57 else
    frictionSpeed (frictionDir (ram 0x0C) (ram 0x490) (ram 0x57)) (ram 0x57) (ram 0x705) (ram 0x702)
      (ram 0x701) (ram 0x456) (ram 0x450))

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem jumpSwimSub_reach (stop : UInt16) (hstop : ∀ a : UInt16, (0xB376 ≤ a && a ≤ 0xC046) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x3376 jumpSwimCode) (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hvcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hI : (p &&& 4 == 0) = false) (hswim : ram 0x704 = 0) (hjs : ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 300)).run ⟨⟨0xB376, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ JumpSwimSummary ram t := by
  simp only [CodeAt, jumpSwimCode, UInt16.reduceAdd] at hcode
  -- The callees' RTS bytes, which this routine executes after each call.
  have hfrts : prg 0x3623 = 0x60 := by
    have h := hfcode; simp only [CodeAt, imposeFrictionCode, UInt16.reduceAdd] at h; exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hhrts : prg 0x3F4C = 0x60 := by
    have h := hhcode; simp only [CodeAt, movePlayerHorizontallyCode, moveObjectHorizontallyCode,
      List.cons_append, List.nil_append, UInt16.reduceAdd] at h
    exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 300)).run ⟨⟨0xB376, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hfrts, hhrts, hI, frictionRam, mphRam, mpvRam] until 49222
    calls [imposeFriction_call, movePlayerHorizontally_call, movePlayerVertically_call]
  all_goals
    intros
    clear hcode hfrts hhrts
    subst hrun
    reach_finish [JumpSwimSummary, jssForce, gravityRam, mpvRam, mphRam, frictionRam, gravityVel, gravityY,
      gravityA, ypos24, yvel16, sext16, dummyIdx, yForceIdx, ySpeedIdx, yPosIdx, yHighIdx, mphPos, mphLo,
      mphHi, mphCarry, pos24, sext, pageIdx, posIdx, forceIdx, speedIdx, frictionSpeed, frictionForce,
      frictionAbs, frictionClamped, frictionRaw, frictionDir]

end Smb.Routine
