import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# Jump start: the vertical half of `PlayerPhysicsSub` (`$B450`–`$B51B`)

Every frame, before Mario moves, `PlayerPhysicsSub` decides whether a jump (or swim stroke)
starts. If so it sets the whole vertical state from tables indexed by a *jump class*: the
horizontal speed class on land (thresholds `$09`, `$10`, `$19`, `$1C`), 5 or 6 in water.

```
CheckForJumping:  no jump if JumpspringAnimCtrl ≠ 0, A not pressed, or A held since last frame
ProcJumping:      on the ground, or swimming and (JumpSwimTimer ≠ 0 or not rising) → InitJS
InitJS:           JumpSwimTimer := $20; YMF_Dummy := 0; Y_MoveForce := 0; JumpOrigin := Y
                  Player_State := 1; class from Player_XSpeedAbsolute (or swimming/whirlpool)
GetYPhy:          VerticalForce, VerticalForceDown, Y_MoveForce, Y_Speed from the tables
                  (swimming near the surface: Y_Speed := 0)
```

This part ends at `X_Physics` (`$B51C`), which only sets horizontal limits and friction.
The climbing branch (`Player_State = 3`) returns early and is excluded here.

Why it matters: a jump resets the sub-pixel `YMF_Dummy` and the force to 0, and every land
force is a multiple of 8. Whether Mario can ever be in the state the floor clip needs
(speed 5.8 at sub-pixel 248) is a question about what follows from these resets.
-/
namespace Smb.Routine

/-- `$B424`–`$B51B`: the physics tables (`JumpMForceData` … `Climb_Y_MForceData`), then the
code up to `X_Physics`. -/
def jumpStartCode : List UInt8 :=
  smbPrg% 0xB424 248

def jumpClass (swim whirl xabs : UInt8) : UInt8 :=
  bif swim != 0 then (bif whirl != 0 then 6 else 5) else
  bif xabs < 0x09 then 0 else bif xabs < 0x10 then 1 else bif xabs < 0x19 then 2 else
  bif xabs < 0x1C then 3 else 4

/-- A 7-entry table indexed by the jump class. -/
def tbl7 (t0 t1 t2 t3 t4 t5 t6 : UInt8) (c : UInt8) : UInt8 :=
  bif c == 0 then t0 else bif c == 1 then t1 else bif c == 2 then t2 else bif c == 3 then t3 else
  bif c == 4 then t4 else bif c == 5 then t5 else t6

def jumpMForce := tbl7 0x20 0x20 0x1E 0x28 0x28 0x0D 0x04
def fallMForce := tbl7 0x70 0x70 0x60 0x90 0x90 0x0A 0x09
def jumpYSpeed := tbl7 0xFC 0xFC 0xFC 0xFB 0xFB 0xFE 0xFF
def initMForce := tbl7 0x00 0x00 0x00 0x00 0x00 0x80 0x00

/-- Does a jump or swim stroke start this frame? -/
def startsJump (ram : UInt16 → UInt8) : Bool :=
  ram 0x70E == 0 && ram 0x0A &&& 0x80 != 0 && ram 0x0A &&& 0x80 &&& ram 0x0D == 0 &&
  (ram 0x1D == 0 || (ram 0x704 != 0 && (ram 0x782 != 0 || ram 0x9F < 0x80)))

/-- RAM after the jump part (`$B450`–`$B51B`). -/
def jumpRam (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  let c := jumpClass (ram 0x704) (ram 0x47D) (ram 0x700)
  let j := startsJump ram
  bif j && i == 0x416 then 0
  else bif j && i == 0x433 then initMForce c
  else bif j && i == 0x709 then jumpMForce c
  else bif j && i == 0x70A then fallMForce c
  else bif j && i == 0x9F then (bif ram 0x704 != 0 && ram 0xCE < 0x14 then 0 else jumpYSpeed c)
  else bif j && i == 0x1D then 1
  else bif j && i == 0x782 then 0x20
  else bif j && i == 0x707 then ram 0xB5
  else bif j && i == 0x708 then ram 0xCE
  else bif j && i == 0x706 then 1
  else bif j && i == 0xFF then
    (bif ram 0x704 != 0 then 0x04 else bif ram 0x754 == 0 then 0x01 else 0x80)
  else ram i

-- The linter walks the large symbolic-execution proofs for nothing.
set_option linter.unusedVariables false

-- Check land and swimming as separate proofs. Splitting before symbolic
-- execution avoids one giant kernel term; the public call theorem is unchanged.
set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
private theorem jumpPart_call_land (stop : UInt16) (hstop : ∀ a : UInt16, (0xB450 ≤ a && a ≤ 0xB51C) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x3424 jumpStartCode) (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D ≠ 3) (hmode : ram 0x704 = 0) :
    ∃ j p' a' y' c', ((CPU.runTo (σ := Plain) stop (m + 80)).run ⟨⟨0xB450, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xB51C, a', x, y', sp, p'⟩, jumpRam ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, jumpStartCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 80)).run ⟨⟨0xB450, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI, hmode] until 46364
  all_goals
    intros
    clear hcode
    subst hrun
    call_finish [jumpRam, jumpClass, tbl7, jumpMForce, fallMForce, jumpYSpeed, initMForce, startsJump]

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
private theorem jumpPart_call_swim (stop : UInt16) (hstop : ∀ a : UInt16, (0xB450 ≤ a && a ≤ 0xB51C) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x3424 jumpStartCode) (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D ≠ 3) (hmode : ram 0x704 ≠ 0) :
    ∃ j p' a' y' c', ((CPU.runTo (σ := Plain) stop (m + 80)).run ⟨⟨0xB450, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xB51C, a', x, y', sp, p'⟩, jumpRam ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, jumpStartCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 80)).run ⟨⟨0xB450, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI, hmode] until 46364
  all_goals
    intros
    clear hcode
    subst hrun
    call_finish [jumpRam, jumpClass, tbl7, jumpMForce, fallMForce, jumpYSpeed, initMForce, startsJump]

theorem jumpPart_call (stop : UInt16) (hstop : ∀ a : UInt16, (0xB450 ≤ a && a ≤ 0xB51C) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x3424 jumpStartCode) (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D ≠ 3) :
    ∃ j p' a' y' c', ((CPU.runTo (σ := Plain) stop (m + 80)).run ⟨⟨0xB450, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xB51C, a', x, y', sp, p'⟩, jumpRam ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  by_cases hmode : ram 0x704 = 0
  · exact jumpPart_call_land stop hstop m a x y sp p ram prg cyc bad hcode hI hst hmode
  · exact jumpPart_call_swim stop hstop m a x y sp p ram prg cyc bad hcode hI hst hmode

/-- What `jumpPart_call`'s closed form says: a jump sets the vertical state from the tables
for its class; without one nothing changes; with one only these bytes and the sound queue. -/
theorem jumpRam_spec (ram : UInt16 → UInt8) :
    let c := jumpClass (ram 0x704) (ram 0x47D) (ram 0x700)
    let r := jumpRam ram
    (startsJump ram = true →
      r 0x416 = 0 ∧ r 0x433 = initMForce c ∧ r 0x709 = jumpMForce c ∧ r 0x70A = fallMForce c ∧
      r 0x9F = (bif ram 0x704 != 0 && ram 0xCE < 0x14 then 0 else jumpYSpeed c) ∧
      r 0x1D = 1 ∧ r 0x782 = 0x20 ∧ r 0x707 = ram 0xB5 ∧ r 0x708 = ram 0xCE ∧ r 0x706 = 1) ∧
    (∀ i : UInt16, (startsJump ram = false ∨ (i ≠ 0x416 ∧ i ≠ 0x433 ∧ i ≠ 0x709 ∧ i ≠ 0x70A ∧
        i ≠ 0x9F ∧ i ≠ 0x1D ∧ i ≠ 0x782 ∧ i ≠ 0x707 ∧ i ≠ 0x708 ∧ i ≠ 0x706 ∧ i ≠ 0xFF)) →
      r i = ram i) := by
  simp only [jumpRam, bne]
  generalize startsJump ram = j
  generalize jumpClass (ram 0x704) (ram 0x47D) (ram 0x700) = c
  refine ⟨fun hj => ?_, fun i hi => ?_⟩ <;> bv_decide

end Smb.Routine
