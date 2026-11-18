import Smb.Routine.ImposeGravity

/-!
# `ImposeGravity` as a callable summary

For use by `sym_run … calls`: from the entry, any caller's run (whose `stop` lies outside the
routine) reaches the RTS address `$C046` in the closed-form state below, whatever path the
routine takes inside. Its branches are folded into the values (`gravityVel`, `gravityA`,
`gravityCycles`), so a caller sees one path instead of up to twelve. The flags are left
unspecified (`p'`), except that the I flag stays set.
-/
namespace Smb.Routine

/-- `Y` (and `$07`) on return: the speed's sign byte, or `-max` after the upward part. -/
def gravityY (aIn mx spd : UInt8) : UInt8 :=
  bif aIn == 0 then (bif 0x80 ≤ spd then 0xFF else 0) else 0 - mx

/-- RAM on return. -/
def gravityRam (aIn x sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  let pos := (ypos24 ram x + sext16 (yvel16 ram x)) &&& 0xFFFFFF
  let vel := gravityVel aIn (ram 0) (ram 1) (ram 2) (yvel16 ram x)
  bif i == dummyIdx x then pos.toUInt8
  else bif i == yPosIdx x then (pos >>> 8).toUInt8
  else bif i == yHighIdx x then (pos >>> 16).toUInt8
  else bif i == yForceIdx x then vel.toUInt8
  else bif i == ySpeedIdx x then (vel >>> 8).toUInt8
  else bif i == 7 then gravityY aIn (ram 2) (ram (ySpeedIdx x))
  else bif i == (0x100 ||| sp.toUInt16) &&& 0x7FF then aIn
  else ram i

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem imposeGravity_call (stop : UInt16) (hstop : ∀ a : UInt16, (0xBFD7 ≤ a && a ≤ 0xC046) = true → a ≠ stop)
    (m : Nat) (aIn x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x3FD7 imposeGravityCode) (hI : (p &&& 4 == 0) = false) (hx : x < 0x32)
    (hspd : ram (ySpeedIdx x) + 0x40 < 0x80) (hmax : ram 2 < 0x40) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 60)).run ⟨⟨0xBFD7, aIn, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xC046, gravityA aIn (ram 0) (ram 1) (ram 2) (yvel16 ram x), x,
        gravityY aIn (ram 2) (ram (ySpeedIdx x)), sp, p'⟩, gravityRam aIn x sp ram, prg,
        cyc + gravityCycles aIn (ram 0) (ram 1) (ram 2) (yvel16 ram x), bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, imposeGravityCode, UInt16.reduceAdd] at hcode
  simp only [ySpeedIdx] at hspd
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 60)).run ⟨⟨0xBFD7, aIn, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI] until 49222
  all_goals
    intros
    clear hcode
    subst hrun
    call_finish [gravityRam, gravityY, gravityA, gravityCycles, gravityVel, ypos24, yvel16, sext16, dummyIdx, yForceIdx, ySpeedIdx, yPosIdx, yHighIdx]

end Smb.Routine
