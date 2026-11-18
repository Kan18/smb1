import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# A Firebar inherits its starting angle (`InitShortFirebar`, `$C45C`)

`FirebarSpinState` is 16 bits: low byte at `$58,x`, high byte (the angle used for drawing and
collision) at `$A0,x`. `$A0,x` is also `Enemy_Y_Speed`. `InitShortFirebar` clears only the low
byte, so a new Firebar starts at whatever *vertical speed* the previous occupant of its enemy
slot left behind (`firebar_inherits`). This is the warpless TAS's 6-4 problem ("the Firebar
inherits the Y speed of the first Podoboo, which is random"), rediscovered as a fact about
the code: the init's frame leaves `$A0 + X` untouched.

```
InitShortFirebar:  $58,x := 0; FirebarSpinSpeed,x / Direction,x from tables by Enemy_ID − $1B
                   Y and X position += 4 (page + carry); TallBBox2: Enemy_BoundBoxCtrl,x := 3
```
-/
namespace Smb.Routine

/-- `$C44F`–`$C487`: `FirebarSpinSpdData`, `FirebarSpinDirData`, `InitShortFirebar`. -/
def firebarInitCode : List UInt8 :=
  smbPrg% 0xC44F 57

/-- `$C7D9`–`$C7DE`: `TallBBox2`. -/
def tallBBox2Code : List UInt8 := smbPrg% 0xC7D9 6

def zpx (base x : UInt8) : UInt16 := (base + x).toUInt16 &&& 0x7FF

def FirebarSummary (x : UInt8) (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xC7DE ∧ t.bad = false ∧
  -- the low byte of the spin state is initialized …
  t.ram (zpx 0x58 x) = 0 ∧
  -- … the high byte, i.e. the angle, is the slot's old `Enemy_Y_Speed`:
  t.ram (zpx 0xA0 x) = ram (zpx 0xA0 x)

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem firebar_inherits (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xC45C ≤ a && a ≤ 0xC487 || 0xC7D9 ≤ a && a ≤ 0xC7DE) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x444F firebarInitCode) (hbcode : CodeAt prg 0x47D9 tallBBox2Code)
    (hI : (p &&& 4 == 0) = false) (hx : x < 0x10) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xC45C, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ FirebarSummary x ram t := by
  simp only [CodeAt, firebarInitCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, tallBBox2Code, UInt16.reduceAdd] at hbcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xC45C, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hbcode, hI] until 51166
  all_goals
    intros
    clear hcode hbcode
    subst hrun
    reach_finish [FirebarSummary, zpx]

end Smb.Routine
