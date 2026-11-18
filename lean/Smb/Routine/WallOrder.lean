import Smb.Routine.SideCheck

/-!
# The side check's order: a left-probe hit decides alone.

From `sideRam_spec`: when a left probe ends the check (`sideHitProbe` 3 or 4), the right probes' tiles do not
matter, and if Mario moves right (`impedeInto 2 = false`), his X speed and position are unchanged. This is the
rightward wall walk: with a left probe in a solid tile, moving right is never arrested, whatever is on the right.
-/
namespace Smb.Routine

/-- `sideHitProbe` does not look at the right probes once a left probe has hit. -/
theorem sideHitProbe_left (prg ram : UInt16 → UInt8)
    (h : sideHitProbe prg ram = 3 ∨ sideHitProbe prg ram = 4) : sideOf prg ram = 2 := by
  rcases h with h | h <;> simp [sideOf, h]

/-- A left hit while moving right: X speed and position unchanged, only the collision bit cleared. -/
theorem left_hit_moving_right_free (w : UInt16 → UInt8) (sp : UInt8) (prg ram : UInt16 → UInt8)
    (h : sideHitProbe prg ram = 3 ∨ sideHitProbe prg ram = 4)
    (hb : sideBlocks prg ram = true) (hm : impedeInto 2 ram = false) :
    let r := sideRam w sp prg ram
    r 0x57 = ram 0x57 ∧ r 0x86 = ram 0x86 ∧ r 0x6D = ram 0x6D ∧ r 0x785 = ram 0x785 := by
  intro r
  have hs := sideHitProbe_left prg ram h
  have := (sideRam_spec w sp prg ram).2.2 hb
  simp only [hs] at this
  have h2 := this.2.2.1 hm
  rcases h2 with ⟨a, b, c⟩
  have c' : (sideRam w sp prg ram 0x6D).toUInt16 <<< 8 ||| (sideRam w sp prg ram 0x86).toUInt16 =
      (ram 0x6D).toUInt16 <<< 8 ||| (ram 0x86).toUInt16 := c
  have split : ∀ p x p' x' : UInt8, p'.toUInt16 <<< 8 ||| x'.toUInt16 = p.toUInt16 <<< 8 ||| x.toUInt16 →
      x' = x ∧ p' = p := by
    intro p x p' x' h
    bv_decide
  have := split _ _ _ _ c'
  exact ⟨a, this.1, this.2, b⟩

end Smb.Routine

#print axioms Smb.Routine.left_hit_moving_right_free
