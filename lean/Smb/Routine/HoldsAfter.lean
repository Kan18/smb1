import Smb.Routine.AbsCheck

/-!
# Carrying an entry box across a few known writes

`Collision.acceptedAll` checks that every box at the collision code's return or at `ImpedePlayerMove` covers the next
region's entry box once the code in between (the impede, the RTS steps, the attribute update) has written its few
cells (`coverAfter`), the X speed allowed to have been zeroed. `holds_after` is what that check is worth: a state that
agrees with the box's state outside the written cells, has each zeroed cell 0 or as it was, is at the entry's PC and
stack pointer and within the next region's bounds, lies in the entry box.
-/
namespace Smb.Abs

theorem holds_after {prot prot' : UInt16 → Bool} {g g' : Global} {ram0 : UInt16 → UInt8} {b e : Box} {u w : Plain}
    {written : UInt16 → Bool} (hb : Holds prot g ram0 b u)
    (ha : e.a = .top) (hx : e.x = .top) (hy : e.y = .top)
    {zeroed : UInt16 → Bool}
    (hcells : ∀ c ∈ e.cells, cellCovered g b [] c = true ∧ (written c.1 = false ∨ (zeroed c.1 = true ∧ c.2.mem 0 = true)))
    (hkeep : ∀ i, written i = false → w.ram i = u.ram i) (hzero : ∀ i, zeroed i = true → w.ram i = 0 ∨ w.ram i = u.ram i) (hpc : w.regs.pc = e.pc) (hs : w.regs.s = e.s)
    (hp : e.p.mem w.regs.p = true) (hi : w.regs.p &&& 4 ≠ 0) (hbad : w.bad = false)
    (hglob : ∀ i, (gAt g' i).mem (w.ram i) = true) : Holds prot' g' w.ram e w := by
  refine { pc := hpc, sp := hs, a := ?_, x := ?_, y := ?_, p := hp, i := hi, bad := hbad, cells := ?_, glob := hglob,
           frame := fun _ _ => rfl }
  · rw [ha]; rfl
  · rw [hx]; rfl
  · rw [hy]; rfl
  · intro c hcm
    obtain ⟨hcov, hw⟩ := hcells c hcm
    have h1 := cellCovered_sound hb hcov
    simp only [applyW] at h1
    rcases hw with hw | ⟨hz, h0⟩
    · rw [hkeep _ hw]; exact h1
    · rcases hzero _ hz with e0 | e1
      · rw [e0]; exact h0
      · rw [e1]; exact h1

end Smb.Abs
