import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# `RelativePlayerPosition` (`$F12A`)

The tail's second call (`$AF13`), right before `PlayerGfxHandler`, whose `RenderPlayerSub` copies its result into
`Player_Pos_ForScroll` (`$0755`). That copy is what `XInv`'s scroll clause rests on: `$0755` is Mario's on-screen X as
of the last frame. The routine is `ldx #0`, `ldy #0`, then `GetObjRelativePosition` (`$F171`) through `RelWOfs`
(`$F142`): `Player_Rel_XPos` (`$03AD`) := `$86 − $071C` and `Player_Rel_YPos` (`$03B8`) := `$CE`, so `$03AD` is the
low byte of `pixelP − leftL`.
-/
-- The linter walks the large symbolic-execution proofs for nothing.
set_option linter.unusedVariables false

namespace Smb.Routine.RelativePosition

/-- `$F12A`: `ldx #0`, `ldy #0`, `jmp RelWOfs`. -/
def headCode : List UInt8 := smbPrg% 0xF12A 7
/-- `$F142` `RelWOfs`: `jsr GetObjRelativePosition`, `ldx ObjectOffset`, `rts`. -/
def relWOfsCode : List UInt8 := smbPrg% 0xF142 6
/-- `$F171` `GetObjRelativePosition`. -/
def getRelCode : List UInt8 := smbPrg% 0xF171 15

/-- From `RelativePlayerPosition`'s entry to its final `rts`: `$03AD` is `$86 − $071C`, `$03B8` is `$CE`, `X` is
`ObjectOffset`, and nothing else outside the stack page changes. -/
theorem relPlayer (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x712A headCode ∧ CodeAt prg 0x7142 relWOfsCode ∧ CodeAt prg 0x7171 getRelCode)
    (hI : (p &&& 4 == 0) = false) :
    let t := ((CPU.runTo (σ := Plain) 0xF147 16).run ⟨⟨0xF12A, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2
    t.regs.pc = 0xF147 ∧ t.bad = false ∧ t.regs.s = sp ∧ t.regs.x = ram 0x08 ∧
    t.ram 0x3AD = ram 0x86 - ram 0x71C ∧ t.ram 0x3B8 = ram 0xCE ∧
    (∀ i : UInt16, i ≠ 0x3AD → i ≠ 0x3B8 → i &&& 0x700 ≠ 0x100 → t.ram i = ram i) := by
  obtain ⟨h1, h2, h3⟩ := hcode
  simp only [CodeAt, headCode, relWOfsCode, getRelCode, UInt16.reduceAdd] at h1 h2 h3
  generalize hrun : ((CPU.runTo (σ := Plain) 0xF147 16).run ⟨⟨0xF12A, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  change f.regs.pc = 0xF147 ∧ f.bad = false ∧ f.regs.s = sp ∧ f.regs.x = ram 0x08 ∧
    f.ram 0x3AD = ram 0x86 - ram 0x71C ∧ f.ram 0x3B8 = ram 0xCE ∧
    (∀ i : UInt16, i ≠ 0x3AD → i ≠ 0x3B8 → i &&& 0x700 ≠ 0x100 → f.ram i = ram i)
  sym_run hrun [h1, h2, h3, hI]
  all_goals
    intros
    clear h1 h2 h3
    simp
    refine ⟨by subst_vars; bv_decide, fun i e1 e2 e3 => ?_⟩
    rw [if_neg e1, if_neg e2, if_neg (fun e => e3 (by subst e; bv_decide)),
      if_neg (fun e => e3 (by subst e; bv_decide))]

/-- `$AF13`: `jsr RelativePlayerPosition`, in `GameEngine`. -/
def callCode : List UInt8 := smbPrg% 0xAF13 3

/-- The call at `$AF13`, through its return to `$AF16`: `$03AD` is `$86 − $071C`, and nothing outside the stack page
changes but `$03AD` and `$03B8`. -/
theorem relPlayerCall (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x2F13 callCode ∧ CodeAt prg 0x712A headCode ∧ CodeAt prg 0x7142 relWOfsCode ∧
      CodeAt prg 0x7171 getRelCode)
    (hI : (p &&& 4 == 0) = false) :
    let t := ((CPU.runTo (σ := Plain) 0xAF16 20).run ⟨⟨0xAF13, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2
    t.regs.pc = 0xAF16 ∧ t.bad = false ∧ t.regs.s = sp ∧
    t.ram 0x3AD = ram 0x86 - ram 0x71C ∧
    (∀ i : UInt16, i ≠ 0x3AD → i ≠ 0x3B8 → i &&& 0x700 ≠ 0x100 → t.ram i = ram i) := by
  obtain ⟨h0, h1, h2, h3⟩ := hcode
  simp only [CodeAt, callCode, headCode, relWOfsCode, getRelCode, UInt16.reduceAdd] at h0 h1 h2 h3
  generalize hrun : ((CPU.runTo (σ := Plain) 0xAF16 20).run ⟨⟨0xAF13, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  change f.regs.pc = 0xAF16 ∧ f.bad = false ∧ f.regs.s = sp ∧ f.ram 0x3AD = ram 0x86 - ram 0x71C ∧
    (∀ i : UInt16, i ≠ 0x3AD → i ≠ 0x3B8 → i &&& 0x700 ≠ 0x100 → f.ram i = ram i)
  sym_run hrun [h0, h1, h2, h3, hI]
  all_goals
    intros
    clear h0 h1 h2 h3
    simp
    refine ⟨by subst_vars; bv_decide, fun i e1 e2 e3 => ?_⟩
    repeat rw [if_neg (fun e => e3 (by subst e; bv_decide))]

/-- The four ranges are bytes of the actual cartridge. -/
theorem rel_rom :
    let prg := fun a => Smb.prg.get! (a &&& 0x7FFF).toNat
    CodeAt prg 0x2F13 callCode ∧ CodeAt prg 0x712A headCode ∧ CodeAt prg 0x7142 relWOfsCode ∧
      CodeAt prg 0x7171 getRelCode :=
  ⟨codeAt_of_matches _ _ _ (by native_decide), codeAt_of_matches _ _ _ (by native_decide),
    codeAt_of_matches _ _ _ (by native_decide), codeAt_of_matches _ _ _ (by native_decide)⟩

end Smb.Routine.RelativePosition
