import Smb.Routine.XPhysics

/-!
# `PlayerPhysicsSub` (`$B450`) as a call theorem (not climbing)

Closed form of the whole routine for callers: the jump start (`JumpStart.lean`) followed by
`X_Physics` (`XPhysics.lean`), whose inputs are read *after* the jump part (a jump sets
`Player_State := 1` first, so the same frame's speed limits are the airborne ones). `A`, `Y`,
the flags and the cycle count are left unspecified; `X` is preserved.
-/
namespace Smb.Routine

def physicsRam (ram : UInt16 → UInt8) : UInt16 → UInt8 := xphysRam (jumpRam ram)

set_option linter.unusedVariables false

theorem physics_call (stop : UInt16) (hstop : ∀ a : UInt16, (0xB450 ≤ a && a ≤ 0xB58B) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x3424 physicsCode) (hjcode : CodeAt prg 0x3424 jumpStartCode)
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D ≠ 3) :
    ∃ j p' a' y' c', ((CPU.runTo (σ := Plain) stop (m + 150)).run ⟨⟨0xB450, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xB58B, a', x, y', sp, p'⟩, physicsRam ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 150)).run ⟨⟨0xB450, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hI] until 46475 calls [jumpPart_call, xphys_call]
  all_goals
    intros
    subst hrun
    call_finish [physicsRam]

end Smb.Routine
