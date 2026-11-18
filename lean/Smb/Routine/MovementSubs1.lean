import Smb.Routine.MovementSubs1BigReleased
import Smb.Routine.MovementSubs1BigFresh
import Smb.Routine.MovementSubs1BigHeld
import Smb.Routine.MovementSubs1SmallReleased
import Smb.Routine.MovementSubs1SmallFresh
import Smb.Routine.MovementSubs1SmallHeld

/-! Jumping movement summary: definitions and six independently checked call cases. -/
namespace Smb.Routine

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
theorem ms1_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xB329 ≤ a && a ≤ 0xC046) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x3329 movementSubsCode) (hecode : CodeAt prg 0x0E04 jumpEngineCode)
    (hpcode : CodeAt prg 0x3424 physicsCode) (hjcode : CodeAt prg 0x3424 jumpStartCode)
    (hacode : CodeAt prg 0x358C animSpeedCode) (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hvcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 1) (hsize : ram 0x70B = 0) (hswim : ram 0x704 = 0)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80) :
    ∃ j p' c', ((CPU.runTo (σ := Plain) stop (m + 600)).run ⟨⟨0xB329, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨ms1_pc, ms1_a sp ram,
        ms1_x, ms1_y sp ram, ms1_s sp, p'⟩,
        ms1_ram sp ram, prg, c', ms1_bad⟩).2 ∧ (p' &&& 4 == 0) = false := by
  by_cases hsmall : ram 0x754 = 0
  · by_cases hbutton : ram 0x0A &&& 0x80 = 0
    · exact movementJumpingBigReleased_call stop hstop m a x y sp p ram prg cyc hcode hecode hpcode hjcode hacode hfcode hhcode hvcode hgcode hI hst hsize hswim hjs hspd hsmall hbutton
    · by_cases hheld : ram 0x0A &&& 0x80 &&& ram 0x0D = 0
      · exact movementJumpingBigFresh_call stop hstop m a x y sp p ram prg cyc hcode hecode hpcode hjcode hacode hfcode hhcode hvcode hgcode hI hst hsize hswim hjs hspd hsmall hbutton hheld
      · exact movementJumpingBigHeld_call stop hstop m a x y sp p ram prg cyc hcode hecode hpcode hjcode hacode hfcode hhcode hvcode hgcode hI hst hsize hswim hjs hspd hsmall hbutton hheld
  · by_cases hbutton : ram 0x0A &&& 0x80 = 0
    · exact movementJumpingSmallReleased_call stop hstop m a x y sp p ram prg cyc hcode hecode hpcode hjcode hacode hfcode hhcode hvcode hgcode hI hst hsize hswim hjs hspd hsmall hbutton
    · by_cases hheld : ram 0x0A &&& 0x80 &&& ram 0x0D = 0
      · exact movementJumpingSmallFresh_call stop hstop m a x y sp p ram prg cyc hcode hecode hpcode hjcode hacode hfcode hhcode hvcode hgcode hI hst hsize hswim hjs hspd hsmall hbutton hheld
      · exact movementJumpingSmallHeld_call stop hstop m a x y sp p ram prg cyc hcode hecode hpcode hjcode hacode hfcode hhcode hvcode hgcode hI hst hsize hswim hjs hspd hsmall hbutton hheld

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface ms1
summary_regs ms1

end Smb.Routine
