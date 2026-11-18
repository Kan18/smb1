import Smb.Summary
import Smb.Routine.GroundFrame

/-!
# `PlayerMovementSubs` while swimming (`$0704 ≠ 0`)

Split the flat way, `JumpSwimSub`'s swimming branches multiply with the physics' paths (timed out at 7 minutes). So `swimSub` summarizes `JumpSwimSub` (`$B376`)
alone, and `ms1w` and `ms0w` compose it with `PlayerPhysicsSub`.
-/
namespace Smb.Routine
set_option linter.unusedVariables false

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem swimSub_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xB329 ≤ a && a ≤ 0xC046) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x3329 movementSubsCode)
    (hacode : CodeAt prg 0x358C animSpeedCode) (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hvcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hI : (p &&& 4 == 0) = false) (hswim : (ram 0x704 == 0) = false) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80) :
    ((CPU.runTo (σ := Plain) stop (m + 500)).run ⟨⟨0xB376, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  have hrts : prg 0x35CB = 0x60 ∧ prg 0x3623 = 0x60 ∧ prg 0x3F4C = 0x60 := by
    refine ⟨?_, ?_, ?_⟩
    · have h := hacode; simp only [CodeAt, animSpeedCode, UInt16.reduceAdd] at h; simp [h]
    · have h := hfcode; simp only [CodeAt, imposeFrictionCode, UInt16.reduceAdd] at h; simp [h]
    · have h := hhcode; simp only [CodeAt, movePlayerHorizontallyCode, moveObjectHorizontallyCode,
        List.cons_append, List.nil_append, UInt16.reduceAdd] at h; simp [h]
  obtain ⟨hr1, hr2, hr3⟩ := hrts
  simp only [CodeAt, movementSubsCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 500)).run ⟨⟨0xB376, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary swimSub hrun [hcode, hr1, hr2, hr3, hI, hswim, animRam, frictionRam, mphRam, mpvRam] until [45932, 49222]
    calls [animSpeed_call, imposeFriction_call, movePlayerHorizontally_call, movePlayerVertically_call]
    exact finish (clear hcode hr1 hr2 hr3; exact_finish swimSub)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface swimSub
summary_regs swimSub

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem ms1w_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xB329 ≤ a && a ≤ 0xC046) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x3329 movementSubsCode) (hecode : CodeAt prg 0x0E04 jumpEngineCode)
    (hpcode : CodeAt prg 0x3424 physicsCode) (hjcode : CodeAt prg 0x3424 jumpStartCode)
    (hacode : CodeAt prg 0x358C animSpeedCode) (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hvcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 1) (hsize : ram 0x70B = 0) (hswim : (ram 0x704 == 0) = false)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80) :
    ((CPU.runTo (σ := Plain) stop (m + 800)).run ⟨⟨0xB329, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  have hst' : ram 0x1D ≠ 3 := by rw [hst]; decide
  have hr4 : prg 0x358B = 0x60 := by
    have h := hpcode; simp only [CodeAt, physicsCode, UInt16.reduceAdd] at h; simp [h]
  have hsS : ∀ a : UInt16, (0xB329 ≤ a && a ≤ 0xC046) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  simp only [CodeAt, movementSubsCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, jumpEngineCode, UInt16.reduceAdd] at hecode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 800)).run ⟨⟨0xB329, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary ms1w hrun [hcode, hecode, hr4, hI, hst, physicsRam, jumpRam, xphysRam, jumpYSpeed, jumpClass, tbl7, startsJump] until [45932, 49222]
    calls [physics_call, swimSub_call]
    exact finish (clear hcode hecode hr4; exact_finish ms1w)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface ms1w
summary_regs ms1w

/-- The routine returns with the stack pointer it got. -/
theorem ms1w_s_eq' (sp : UInt8) : ms1w_s sp = sp := by
  delta ms1w_s swimSub_s
  first | rfl | bv_decide

theorem ms1w_no_bad : ms1w_bad = false := by
  delta ms1w_bad swimSub_bad
  first | rfl | decide | bv_decide

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem ms0w_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xB329 ≤ a && a ≤ 0xC046) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x3329 movementSubsCode) (hecode : CodeAt prg 0x0E04 jumpEngineCode)
    (hpcode : CodeAt prg 0x3424 physicsCode) (hjcode : CodeAt prg 0x3424 jumpStartCode)
    (hacode : CodeAt prg 0x358C animSpeedCode) (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hvcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 0) (hsize : ram 0x70B = 0) (hswim : (ram 0x704 == 0) = false)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80) :
    ((CPU.runTo (σ := Plain) stop (m + 800)).run ⟨⟨0xB329, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  have hst' : ram 0x1D ≠ 3 := by rw [hst]; decide
  have hrts : prg 0x35CB = 0x60 ∧ prg 0x3623 = 0x60 ∧ prg 0x3F4C = 0x60 ∧ prg 0x358B = 0x60 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h := hacode; simp only [CodeAt, animSpeedCode, UInt16.reduceAdd] at h; simp [h]
    · have h := hfcode; simp only [CodeAt, imposeFrictionCode, UInt16.reduceAdd] at h; simp [h]
    · have h := hhcode; simp only [CodeAt, movePlayerHorizontallyCode, moveObjectHorizontallyCode,
        List.cons_append, List.nil_append, UInt16.reduceAdd] at h; simp [h]
    · have h := hpcode; simp only [CodeAt, physicsCode, UInt16.reduceAdd] at h; simp [h]
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrts
  have hsS : ∀ a : UInt16, (0xB329 ≤ a && a ≤ 0xC046) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  simp only [CodeAt, movementSubsCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, jumpEngineCode, UInt16.reduceAdd] at hecode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 800)).run ⟨⟨0xB329, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary ms0w hrun [hcode, hecode, hr1, hr2, hr3, hr4, hI, hst, animRam, frictionRam, mphRam, physicsRam, jumpRam, xphysRam, jumpYSpeed, jumpClass, tbl7] until [45932, 49222]
    calls [physics_call, swimSub_call, animSpeed_call, imposeFriction_call, movePlayerHorizontally_call]
    exact finish (clear hcode hecode hr1 hr2 hr3 hr4; exact_finish ms0w)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface ms0w

theorem ms0w_s_eq' (sp : UInt8) (ram : UInt16 → UInt8) : ms0w_s sp ram = sp := by
  delta ms0w_s
  simp only [swimSub_s_eq]
  first | bv_decide (config := { enums := false }) | simp

theorem ms0w_no_bad (sp : UInt8) (ram : UInt16 → UInt8) : ms0w_bad sp ram = false := by
  delta ms0w_bad
  simp only [swimSub_bad_eq]
  first | bv_decide (config := { enums := false }) | simp

end Smb.Routine
