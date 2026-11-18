import Smb.Data.ProofRom
import Smb.Routine.JumpStart

/-!
# Horizontal physics constants: `X_Physics` (`$B51C`, end of `PlayerPhysicsSub`)

Each frame this picks Mario's speed limits and the acceleration/friction step used by
`ImposeFriction`:

- speed class `y`: 0 (running) on the ground facing the held direction with B held or the
  running timer set, or in the air at `|X speed| ≥ $19`; 2 in water areas on the ground;
  otherwise 1 (walking);
- `MaximumLeftSpeed` = `[$D8, $E8, $F0][y]`, `MaximumRightSpeed` = `[$28, $18, $10][y]`
  (`$0C` during the pipe entrance, routine 7);
- friction class `f`: 0 when running (as above), otherwise 1, or 2 if `RunningSpeed` is set
  or `|X speed| ≥ $21`; `FrictionAdder` = `[$E4, $98, $D0][f]` (8.8: `$00.xx`),
  **doubled** when `PlayerFacingDir ≠ Player_MovingDir` (turning around: `$D0` → 1.160);
- B held on the ground facing the held direction sets `RunningTimer := $0A`.
-/
namespace Smb.Routine

/-- `$B424`–`$B58B`: the physics tables and all of `PlayerPhysicsSub`. -/
def physicsCode : List UInt8 :=
  smbPrg% 0xB424 360

/-- Running: the class-0 conditions (also the ones that skip the friction class). -/
def xRunning (ram : UInt16 → UInt8) : Bool :=
  bif ram 0x1D == 0 then
    ram 0x74E != 0 && ram 0x0C == ram 0x45 && (ram 0x0A &&& 0x40 != 0 || ram 0x783 != 0)
  else 0x19 ≤ ram 0x700

def xSpeedClass (ram : UInt16 → UInt8) : UInt8 :=
  bif xRunning ram then 0 else bif ram 0x1D == 0 && ram 0x74E == 0 then 2 else 1

def xFrictionClass (ram : UInt16 → UInt8) : UInt8 :=
  bif xRunning ram then 0 else bif ram 0x703 != 0 || 0x21 ≤ ram 0x700 then 2 else 1

def tbl3 (a b c : UInt8) (i : UInt8) : UInt8 := bif i == 0 then a else bif i == 1 then b else c

/-- RAM after `X_Physics`, from the RAM it starts with. -/
def xphysRam (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  let lo := tbl3 0xE4 0x98 0xD0 (xFrictionClass ram)
  let turning := ram 0x33 != ram 0x45
  bif i == 0 then xFrictionClass ram
  else bif i == 0x450 then tbl3 0xD8 0xE8 0xF0 (xSpeedClass ram)
  else bif i == 0x456 then (bif ram 0x0E == 7 then 0x0C else tbl3 0x28 0x18 0x10 (xSpeedClass ram))
  else bif i == 0x702 then (bif turning then lo <<< 1 else lo)
  else bif i == 0x701 then (bif turning then lo >>> 7 else 0)
  else bif i == 0x783 && ram 0x1D == 0 && ram 0x74E != 0 && ram 0x0C == ram 0x45 && ram 0x0A &&& 0x40 != 0
    then 0x0A
  else ram i

set_option linter.unusedVariables false

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
theorem xphys_call (stop : UInt16) (hstop : ∀ a : UInt16, (0xB51C ≤ a && a ≤ 0xB58B) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x3424 physicsCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j p' a' y' c', ((CPU.runTo (σ := Plain) stop (m + 60)).run ⟨⟨0xB51C, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xB58B, a', x, y', sp, p'⟩, xphysRam ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, physicsCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 60)).run ⟨⟨0xB51C, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI] until 46475
  all_goals
    intros
    clear hcode
    subst hrun
    call_finish [xphysRam, xFrictionClass, xSpeedClass, xRunning, tbl3]

/-- What `xphys_call`'s closed form says, field by field. -/
theorem xphysRam_spec (ram : UInt16 → UInt8) :
    let r := xphysRam ram
    let y := xSpeedClass ram
    let lo := tbl3 0xE4 0x98 0xD0 (xFrictionClass ram)
    let turning := ram 0x33 != ram 0x45
    r 0x450 = tbl3 0xD8 0xE8 0xF0 y ∧
    r 0x456 = (bif ram 0x0E == 7 then 0x0C else tbl3 0x28 0x18 0x10 y) ∧
    r 0x702 = (bif turning then lo <<< 1 else lo) ∧
    r 0x701 = (bif turning then lo >>> 7 else 0) ∧
    r 0x783 = (bif ram 0x1D == 0 && ram 0x74E != 0 && ram 0x0C == ram 0x45 && ram 0x0A &&& 0x40 != 0
      then 0x0A else ram 0x783) := by
  simp [xphysRam]

end Smb.Routine
