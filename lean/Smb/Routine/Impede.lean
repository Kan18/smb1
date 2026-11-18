import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# `ImpedePlayerMove` (`$DF4B`): walls, and failed landings

Entered with `$00` = the side that collided (1 = the left side … 2 = the right side; a failed
landing passes `Player_MovingDir` here). If Mario is moving *into* that side:
`X speed := 0`, `SideCollisionTimer := $10`, and he is pushed one pixel back (with the page).
Either way the corresponding bit of `Player_CollisionBits` is cleared.

For a failed landing (feet in a solid metatile at row offset ≥ 5, `ChkFootMTile`) this means:
while Mario falls through a clipped floor, every frame his feet are in the block costs his
horizontal speed if he moves in his moving direction, and moves him one pixel back. Speed 0
counts as moving into the wall (the tests are sign tests of `speed` and `speed − 1`), so even
standing still horizontally he is pushed one pixel per frame.
-/
namespace Smb.Routine

/-- `$DF4B`–`$DF8A`. -/
def impedeCode : List UInt8 := smbPrg% 0xDF4B 64

/-- Is Mario moving into the collided side? (Sign tests: `speed` for the left side, `speed − 1`
for the right side; so speed 0 counts as moving into either side.) -/
def impedes (ram : UInt16 → UInt8) : Bool :=
  bif ram 0 == 1 then ram 0x57 < 0x80 else (ram 0x57 - 1) &&& 0x80 != 0

def ImpedeSummary (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  let back : UInt16 := bif ram 0 == 1 then 0xFFFF else 1
  let pos : UInt16 := ((ram 0x6D).toUInt16 <<< 8 ||| (ram 0x86).toUInt16) + back
  t.regs.pc = 0xDF8A ∧ t.bad = false ∧
  (impedes ram = true → t.ram 0x57 = 0 ∧ t.ram 0x785 = 0x10 ∧ t.ram 0x86 = pos.toUInt8 ∧
     t.ram 0x6D = (pos >>> 8).toUInt8) ∧
  (impedes ram = false → t.ram 0x57 = ram 0x57 ∧ t.ram 0x86 = ram 0x86)

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem impede_reach (stop : UInt16) (hstop : ∀ a : UInt16, (0xDF4B ≤ a && a ≤ 0xDF8A) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x5F4B impedeCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xDF4B, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ ImpedeSummary ram t := by
  simp only [CodeAt, impedeCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xDF4B, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hI] until 57226
  all_goals
    intros
    clear hcode
    subst hrun
    reach_finish [ImpedeSummary, impedes]

end Smb.Routine
