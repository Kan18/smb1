import Smb.Summary
import Smb.Routine.MovementSubs0Finish
import Smb.Routine.MovementSubs1Defs

namespace Smb.Routine

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
theorem movementJumpingBigFresh_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xB329 ≤ a && a ≤ 0xC046) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x3329 movementSubsCode) (hecode : CodeAt prg 0x0E04 jumpEngineCode)
    (hpcode : CodeAt prg 0x3424 physicsCode) (hjcode : CodeAt prg 0x3424 jumpStartCode)
    (hacode : CodeAt prg 0x358C animSpeedCode) (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hvcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 1) (hsize : ram 0x70B = 0) (hswim : ram 0x704 = 0)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hsmall : ram 0x754 = 0) (hbutton : ram 0x0A &&& 0x80 ≠ 0) (hheld : ram 0x0A &&& 0x80 &&& ram 0x0D = 0) :
    ∃ j p' c', ((CPU.runTo (σ := Plain) stop (m + 600)).run ⟨⟨0xB329, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨ms1_pc, ms1_a sp ram,
        ms1_x, ms1_y sp ram, ms1_s sp, p'⟩,
        ms1_ram sp ram, prg, c', ms1_bad⟩).2 ∧ (p' &&& 4 == 0) = false := by
  have hst' : ram 0x1D ≠ 3 := by rw [hst]; decide
  have hrts : prg 0x35CB = 0x60 ∧ prg 0x3623 = 0x60 ∧ prg 0x3F4C = 0x60 ∧ prg 0x358B = 0x60 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h := hacode; simp only [CodeAt, animSpeedCode, UInt16.reduceAdd] at h; simp [h]
    · have h := hfcode; simp only [CodeAt, imposeFrictionCode, UInt16.reduceAdd] at h; simp [h]
    · have h := hhcode; simp only [CodeAt, movePlayerHorizontallyCode, moveObjectHorizontallyCode,
        List.cons_append, List.nil_append, UInt16.reduceAdd] at h; simp [h]
    · have h := hpcode; simp only [CodeAt, physicsCode, UInt16.reduceAdd] at h; simp [h]
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrts
  simp only [CodeAt, movementSubsCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, jumpEngineCode, UInt16.reduceAdd] at hecode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 600)).run ⟨⟨0xB329, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hecode, hr1, hr2, hr3, hr4, hI, hst, hswim, physicsRam, jumpRam, xphysRam, animRam,
      jumpYSpeed, jumpClass, tbl7, startsJump, frictionRam, mphRam, mpvRam] until [45932, 49222]
    calls [physics_call, animSpeed_call, imposeFriction_call, movePlayerHorizontally_call,
      movePlayerVertically_call]
  all_goals
    intros
    clear hcode hecode hr1 hr2 hr3 hr4
    settle_run_bad hrun
    exact_finish ms1

end Smb.Routine
