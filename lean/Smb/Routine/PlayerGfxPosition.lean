import Smb.Data.ProofRom
import Smb.Routine.Common
import Smb.Game

/-! The graphics routine's saved horizontal coordinate. Drawing copies `$03AD`
to `$0755`, but invulnerability blinking can return before that copy. A
run-level screen-position invariant must account for this skipped refresh. -/
namespace Smb.Routine

def playerGfxBlinkCode : List UInt8 :=
  smbPrg% 0xEEE9 10
def playerGfxSaveXCode : List UInt8 := smbPrg% 0xEFC0 6

theorem rom_playerGfxBlinkCode : CodeAt (fun a => Smb.prg.get! (a &&& 0x7FFF).toNat) 0x6EE9 playerGfxBlinkCode :=
  codeAt_of_matches _ _ _ (by native_decide)
theorem rom_playerGfxSaveXCode : CodeAt (fun a => Smb.prg.get! (a &&& 0x7FFF).toNat) 0x6FC0 playerGfxSaveXCode :=
  codeAt_of_matches _ _ _ (by native_decide)

/- The blink branch reaches the RTS with RAM unchanged, including `$0755`.
This is a local call theorem, not a claim that arbitrary entry RAM is reachable. -/
set_option maxRecDepth 20000 in
theorem playerGfx_blink_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xEEE9 ≤ a && a ≤ 0xEEF2) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x6EE9 playerGfxBlinkCode)
    (hI : (p &&& 4 == 0) = false) (htimer : ram 0x79E ≠ 0)
    (hodd : ram 0x09 &&& 1 = 1) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 10)).run
      ⟨⟨0xEEE9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run
        ⟨⟨0xEF33, ram 0x09 >>> 1, x, y, sp, p'⟩, ram, prg, cyc + 15, false⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, playerGfxBlinkCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 10)).run
    ⟨⟨0xEEE9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hI, htimer, hodd] until [61235, 61171]
  all_goals
    intros
    try { subst_vars; bv_decide }
    clear hcode
    subst hrun
    call_finish []

def playerGfxSavedX (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  bif i == 0x755 then ram 0x3AD else ram i

set_option maxRecDepth 20000 in
theorem playerGfx_saveX_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xEFC0 ≤ a && a ≤ 0xEFC5) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x6FC0 playerGfxSaveXCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 4)).run
      ⟨⟨0xEFC0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run
        ⟨⟨0xEFC6, ram 0x3AD, x, y, sp, p'⟩, playerGfxSavedX ram, prg, cyc + 8, false⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, playerGfxSaveXCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 4)).run
    ⟨⟨0xEFC0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hI] until 61382
  all_goals
    intros
    try { subst_vars; bv_decide }
    clear hcode
    subst hrun
    call_finish [playerGfxSavedX]

end Smb.Routine
