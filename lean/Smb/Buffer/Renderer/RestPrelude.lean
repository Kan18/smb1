import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
The straight-line suffix after the graphics-pointer high byte is stored.
This is the remaining seam between `PointerIndex` and `TilePair`.
-/
namespace Smb.Buffer.Renderer.RestPrelude
open Smb Smb.Routine Smb.Symbolic

def code : List UInt8 :=
  smbPrg% 0x88E7 18
def rom (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat
theorem code_in_rom : CodeAt rom 0x08e7 code :=
  codeAt_of_matches _ _ _ (by native_decide)

set_option maxHeartbeats 4000000 in
theorem reaches_tile_pair (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08e7 code) (hI : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x88e7, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x88f9 11).run s).2
    t.bad = false ∧ t.regs.pc = 0x88f9 ∧
      t.ram 0 = ram 0 ∧ t.ram 1 = ram 1 ∧ t.ram 7 = ram 7 := by
  dsimp only
  simp only [CodeAt, code, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x88f9 11).run
    ⟨⟨0x88e7, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hr [hc, hi] until 0x88f9
  all_goals
    intros
    clear hc hi
    subst hr
    rw [runTo_snd_stop _ 0x88f9 _ rfl]
    simp_all (config := { maxSteps := 1000000 })


set_option maxHeartbeats 4000000 in
theorem reaches_tile_pair_keeps_I (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08e7 code) (hI : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x88e7, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x88f9 11).run s).2
    t.regs.p &&& 4 ≠ 0 := by
  dsimp only
  simp only [CodeAt, code, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x88f9 11).run
    ⟨⟨0x88e7, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hr [hc, hi] until 0x88f9
  all_goals
    intros
    clear hc hi
    subst hr
    rw [runTo_snd_stop _ 0x88f9 _ rfl]
    dsimp only
    bv_decide


set_option maxHeartbeats 4000000 in
theorem reaches_tile_pair_keeps_prg (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08e7 code) (hI : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x88e7, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x88f9 11).run s).2
    t.prg = prg := by
  dsimp only
  simp only [CodeAt, code, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x88f9 11).run
    ⟨⟨0x88e7, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hr [hc, hi] until 0x88f9
  all_goals
    intros
    clear hc hi
    subst hr
    rw [runTo_snd_stop _ 0x88f9 _ rfl]

end Smb.Buffer.Renderer.RestPrelude
