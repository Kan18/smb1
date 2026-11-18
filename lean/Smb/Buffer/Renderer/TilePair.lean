import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
The two actual tile reads/stores between the row prelude and attribute work.
The graphics pointer high byte is assumed to be `$8B` or `$8C`, as the ROM
tables at `$8B0C` select for the renderer's four attribute classes.  The
table-to-pointer derivation is a separate source obligation.
-/
namespace Smb.Buffer.Renderer.TilePair
open Smb Smb.Routine Smb.Symbolic

def code : List UInt8 :=
  smbPrg% 0x88F9 13

def rom (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

theorem code_in_rom : CodeAt rom 0x08f9 code :=
  codeAt_of_matches _ _ _ (by native_decide)

set_option maxHeartbeats 5000000 in
theorem two_tile_writes_keep_offset (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08f9 code) (hI : p &&& 4 ≠ 0)
    (hptr : ram 7 = 0x8b ∨ ram 7 = 0x8c) :
    let s : Plain := ⟨⟨0x88f9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x8906 8).run s).2
    t.bad = false ∧ t.regs.pc = 0x8906 ∧ t.regs.x = ram 0 ∧
      t.ram 0 = ram 0 ∧ t.ram 1 = ram 1 := by
  dsimp only
  rcases hptr with hptr | hptr
  all_goals
    simp only [CodeAt, code, UInt16.reduceAdd] at hc
    generalize hr : ((CPU.runTo (σ := Plain) 0x8906 8).run
      ⟨⟨0x88f9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
    have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
    sym_run hr [hc, hi, hptr] until 0x8906
    all_goals
      intros
      clear hc hi
      subst hr
      rw [runTo_snd_stop _ 0x8906 _ rfl]
      simp_all (config := { maxSteps := 1000000 })
      bv_decide


set_option maxHeartbeats 5000000 in
theorem two_tile_writes_keep_I (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08f9 code) (hI : p &&& 4 ≠ 0)
    (hptr : ram 7 = 0x8b ∨ ram 7 = 0x8c) :
    let s : Plain := ⟨⟨0x88f9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x8906 8).run s).2
    t.regs.p &&& 4 ≠ 0 := by
  dsimp only
  rcases hptr with hptr | hptr
  all_goals
    simp only [CodeAt, code, UInt16.reduceAdd] at hc
    generalize hr : ((CPU.runTo (σ := Plain) 0x8906 8).run
      ⟨⟨0x88f9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
    have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
    sym_run hr [hc, hi, hptr] until 0x8906
    all_goals
      intros
      clear hc hi
      subst hr
      rw [runTo_snd_stop _ 0x8906 _ rfl]
      dsimp only
      bv_decide

set_option maxHeartbeats 5000000 in
theorem two_tile_writes_keep_prg (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08f9 code) (hI : p &&& 4 ≠ 0)
    (hptr : ram 7 = 0x8b ∨ ram 7 = 0x8c) :
    let s : Plain := ⟨⟨0x88f9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x8906 8).run s).2
    t.prg = prg := by
  dsimp only
  rcases hptr with hptr | hptr
  all_goals
    simp only [CodeAt, code, UInt16.reduceAdd] at hc
    generalize hr : ((CPU.runTo (σ := Plain) 0x8906 8).run
      ⟨⟨0x88f9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
    have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
    sym_run hr [hc, hi, hptr] until 0x8906
    all_goals
      intros
      clear hc hi
      subst hr
      rw [runTo_snd_stop _ 0x8906 _ rfl]


end Smb.Buffer.Renderer.TilePair
