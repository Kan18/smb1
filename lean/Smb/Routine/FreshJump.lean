import Smb.Routine.MovementSubs0
import Smb.Routine.VerticalPhase

/-!
# The first movement of a fresh jump

Project gravity and position from the existing exact `ms0_ram`, then reuse
`ms0_call` to attach the appropriate vertical invariant to its actual endpoint.
The jump class is selected from the input $0700, before friction changes it.

This covers the fresh-jump branch under the original call theorem's premises.
It does not establish the invariant across later collisions, injuries, freezes,
or a complete NES frame. In particular, the old speed bound remains required
by the reused call theorem even though jump setup overwrites that speed.
-/
namespace Smb.Routine.FreshJump

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The gravity bytes omitted by GroundFrameSummary, projected from the existing
    exact RAM function. All class references use input $700. -/
theorem ms0_fresh_gravity (sp : UInt8) (ram : UInt16 → UInt8)
    (hj : startsJump ram = true) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) :
    let c := jumpClass (ram 0x704) (ram 0x47D) (ram 0x700)
    ms0_ram sp ram 0x709 = (bif ram 0x0E == 0x0B then 0x28 else jumpMForce c) ∧
    ms0_ram sp ram 0x70A = fallMForce c := by
  sym_exec [ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30, startsJump, jumpRam, physicsRam, xphysRam,
    animRam, frictionRam, mphRam, mpvRam, gravityRam, jumpClass, jumpMForce,
    fallMForce, jumpYSpeed, initMForce, tbl7, dummyIdx, yForceIdx, ySpeedIdx, yPosIdx,
    yHighIdx, yvel16, ypos24, sext16, gravityVel, bne] at *
  fun_congr
  bv_decide (config := { enums := false })

/-- Remaining fresh-jump projections, including actual first-frame pixel motion. -/
theorem ms0_fresh_vertical (sp : UInt8) (ram : UInt16 → UInt8)
    (hj : startsJump ram = true) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) :
    let c := jumpClass (ram 0x704) (ram 0x47D) (ram 0x700)
    let g := bif ram 0x0E == 0x0B then 0x28 else jumpMForce c
    ms0_ram sp ram 0x416 = 0 ∧
    yvel16 (ms0_ram sp ram) 0 = gravityVel 0 g 0 4 ((jumpYSpeed c).toUInt16 <<< 8) ∧
    ms0_ram sp ram 0x1D = 1 ∧
    ypos24 (ms0_ram sp ram) 0 =
      ((ypos24 ram 0 &&& (0xFFFF00 : UInt32)) + sext16 ((jumpYSpeed c).toUInt16 <<< 8)) &&& (0xFFFFFF : UInt32) ∧
    ms0_pc sp ram = 0xC046 := by
  sym_exec [ms0_ram, ms0_pc, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30, startsJump, jumpRam, physicsRam, xphysRam,
    animRam, frictionRam, mphRam, mpvRam, gravityRam, jumpClass, jumpMForce,
    fallMForce, jumpYSpeed, initMForce, tbl7, dummyIdx, yForceIdx, ySpeedIdx, yPosIdx,
    yHighIdx, yvel16, ypos24, sext16, gravityVel, bne] at *
  fun_congr
  bv_decide (config := { enums := false })


/-- Regime chosen from the input class, never from final XSpeedAbsolute. -/
def FreshRegime (initial out : UInt16 → UInt8) : Prop :=
  (initial 0x700 < 0x19 →
    VerticalPhase.lowSafe (yvel16 out 0) ∧ out 0x709 ≤ 0x80 ∧ out 0x70A ≤ 0x80) ∧
  (0x19 ≤ initial 0x700 →
    VerticalPhase.safe (out 0x416).toUInt16 (yvel16 out 0) (out 0x709) ∧ out 0x70A = 0x90)

/-- Fresh-jump movement initializes the appropriate invariant on actual output
    bytes, even if mode0B forces28 (the high-class first-step gravity is28 anyway). -/
theorem ms0_fresh_regime (sp : UInt8) (ram : UInt16 → UInt8)
    (hj : startsJump ram = true) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) :
    FreshRegime ram (ms0_ram sp ram) := by
  obtain ⟨ha, hf⟩ := ms0_fresh_gravity sp ram hj hs hz
  obtain ⟨hq, hv, hst, hpos, hpc⟩ := ms0_fresh_vertical sp ram hj hs hz
  unfold FreshRegime
  rw [hq, hv, ha, hf]
  sym_exec [hs, jumpClass, jumpYSpeed, jumpMForce, fallMForce, tbl7,
    gravityVel, VerticalPhase.lowSafe, VerticalPhase.safe, VerticalPhase.phase]
  bv_decide

/-- Reuse the checked real PlayerMovementSubs call theorem. This does not execute
    the frame again; it adds the fresh-jump invariant to its exact end RAM. -/
theorem freshJump_reach (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xB329 ≤ a && a ≤ 0xC046) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x3329 movementSubsCode) (hecode : CodeAt prg 0x0E04 jumpEngineCode)
    (hpcode : CodeAt prg 0x3424 physicsCode) (hjcode : CodeAt prg 0x3424 jumpStartCode)
    (hacode : CodeAt prg 0x358C animSpeedCode) (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hvcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 0) (hsize : ram 0x70B = 0)
    (hswim : ram 0x704 = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hjump : startsJump ram = true) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 600)).run
        ⟨⟨0xB329, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧
      t.regs.pc = 0xC046 ∧ t.bad = false ∧ t.ram = ms0_ram sp ram ∧
      t.ram 0x1D = 1 ∧ t.ram 0x416 = 0 ∧ FreshRegime ram t.ram := by
  obtain ⟨j, p', c', hrun, hp'⟩ := ms0_call stop hstop m a x y sp p ram prg cyc
    hcode hecode hpcode hjcode hacode hfcode hhcode hvcode hgcode hI hst hsize hswim hjs hspd
  refine ⟨j, ⟨⟨ms0_pc sp ram, ms0_a sp ram, ms0_x x sp ram, ms0_y sp ram,
    ms0_s sp, p'⟩, ms0_ram sp ram, prg, c', ms0_bad⟩, hrun, ?_⟩
  obtain ⟨hq, hv, hstate, hpos, hpc⟩ := ms0_fresh_vertical sp ram hjump hswim hsize
  exact ⟨hpc, ms0_bad_eq, rfl, hstate, hq, ms0_fresh_regime sp ram hjump hswim hsize⟩


end Smb.Routine.FreshJump
