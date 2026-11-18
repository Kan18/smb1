import Smb.Routine.AbsCheck

/-!
Restore entry constraints on protected cells from the region's saved RAM.
This lets an exact parser tuple be carried through a region without multiplying
all of that region's boxes by every tuple. The caller must still establish the
saved tuple and the unprotected part of the next entry contract.
-/
namespace Smb.Abs

/-- Remove the constraints that can instead be supplied by saved protected RAM. -/
def Box.withoutProtected (b : Box) (prot : UInt16 → Bool) : Box :=
  { b with cells := b.cells.filter fun c => !prot c.1 }

/-- Restore an entire entry, including correlations represented by the choice
of `e`, from its unprotected constraints and the same saved tuple. -/
theorem Holds.restoreProtected {prot : UInt16 → Bool} {g : Global}
    {ram0 : UInt16 → UInt8} {e : Box} {s : Plain}
    (h : Holds prot g ram0 (e.withoutProtected prot) s)
    (saved : ∀ c ∈ e.cells, prot c.1 = true → c.2.mem (ram0 c.1) = true) :
    Holds prot g ram0 e s := by
  refine { h with cells := ?_ }
  intro c hc
  cases hp : prot c.1 with
  | false =>
    exact h.cells c (by simpa [Box.withoutProtected, hp] using hc)
  | true =>
    rw [h.frame c.1 hp]
    exact saved c hc hp

/-- Restore only a selected subset of protected cells. This avoids asking for
saved values of unrelated protected cells already covered by the source box. -/
theorem Holds.restoreKept {prot keep : UInt16 → Bool} {g : Global}
    {ram0 : UInt16 → UInt8} {e : Box} {s : Plain}
    (hk : ∀ i, keep i = true → prot i = true)
    (h : Holds prot g ram0 (e.withoutProtected keep) s)
    (saved : ∀ c ∈ e.cells, keep c.1 = true → c.2.mem (ram0 c.1) = true) :
    Holds prot g ram0 e s := by
  refine { h with cells := ?_ }
  intro c hc
  cases hp : keep c.1 with
  | false => exact h.cells c (by simpa [Box.withoutProtected, hp] using hc)
  | true =>
    rw [h.frame c.1 (hk c.1 hp)]
    exact saved c hc hp

/-- A checked box inclusion transfers all ordinary constraints. -/
theorem Holds.of_le {prot : UInt16 → Bool} {g : Global}
    {ram0 : UInt16 → UInt8} {b e : Box} {s : Plain}
    (h : Holds prot g ram0 b s) (hle : Box.le g b e = true) :
    Holds prot g ram0 e s := by
  simp only [Box.le, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hle
  obtain ⟨⟨⟨⟨⟨⟨hpc, hs⟩, ha⟩, hx⟩, hy⟩, hp⟩, hcells⟩ := hle
  exact {
    pc := h.pc.trans hpc.symm
    sp := h.sp.trans hs.symm
    a := VS.sub_sound ha h.a
    x := VS.sub_sound hx h.x
    y := VS.sub_sound hy h.y
    p := VS.sub_sound hp h.p
    i := h.i
    bad := h.bad
    cells := fun d hd => by simpa [applyW] using cellCovered_sound h (hcells d hd)
    glob := h.glob
    frame := h.frame }

/-- The successor need only contain the unprotected part of the chosen entry.
Its protected constraints come from the original tuple, not a Cartesian merge. -/
theorem Holds.link_kept {prot : UInt16 → Bool} {g : Global}
    {ram0 : UInt16 → UInt8} {b e : Box} {s : Plain}
    (h : Holds prot g ram0 b s)
    (hle : Box.le g b (e.withoutProtected prot) = true)
    (saved : ∀ c ∈ e.cells, prot c.1 = true → c.2.mem (ram0 c.1) = true) :
    Holds prot g ram0 e s :=
  (h.of_le hle).restoreProtected saved

/-- Link using a smaller, explicitly protected saved tuple. -/
theorem Holds.link_kept_subset {prot keep : UInt16 → Bool} {g : Global}
    {ram0 : UInt16 → UInt8} {b e : Box} {s : Plain}
    (h : Holds prot g ram0 b s)
    (hk : ∀ i, keep i = true → prot i = true)
    (hle : Box.le g b (e.withoutProtected keep) = true)
    (saved : ∀ c ∈ e.cells, keep c.1 = true → c.2.mem (ram0 c.1) = true) :
    Holds prot g ram0 e s :=
  (h.of_le hle).restoreKept hk saved

/-- At a new region boundary, begin its protected-memory frame with the
current RAM. This changes no register, cell, or global constraint. -/
theorem Holds.rebase {prot : UInt16 → Bool} {g : Global}
    {ram0 : UInt16 → UInt8} {e : Box} {s : Plain}
    (h : Holds prot g ram0 e s) (nextProt : UInt16 → Bool) :
    Holds nextProt g s.ram e s := by
  exact { h with frame := fun _ _ => rfl }

/-- A kept exact tuple plus an accepted entry implies the target table's
invariant. This does not claim that the tuple was initially reachable. -/
theorem inv_of_kept_entry {prot : UInt16 → Bool} {g : Global} {T : Table}
    {ram0 : UInt16 → UInt8} {e : Box} {s : Plain}
    (hin : entryIn g T e = true)
    (h : Holds prot g ram0 (e.withoutProtected prot) s)
    (saved : ∀ c ∈ e.cells, prot c.1 = true → c.2.mem (ram0 c.1) = true) :
    Inv prot g ram0 T s :=
  inv_of_entry hin (h.restoreProtected saved)

end Smb.Abs
