import Smb.Routine.HorizontalLimit

/-!
# `XInv` from the last frame's `XStep`

`HorizontalLimit`'s frame theorems assume `XInv` at `PlayerCtrlRoutine`'s entry. All of it but the last clause is what
the last frame's routine left (`XStep`), since every region between the two keeps those bytes. The last clause is
about `$0755`, last frame's on-screen X, and `$0785`, the side-collision timer. `xinv_next` shows it holds when the
tail copies the on-screen X into `$0755` (`PlayerGfxHandler`'s `$EFC3`, from `$03AD`, which `RelativePlayerPosition`
computes as the low byte of `X − left edge`), and the timer, if the routine just set it, hasn't run out by the next
entry. The tail skips that copy on blinking frames (`$079E` set, odd frame), which this doesn't cover.
-/
namespace Smb.Routine.HorizontalLimit

theorem xinv_next (ram out next : UInt16 → UInt8) (h : XStep ram out)
    (h57 : next 0x57 = out 0x57) (h86 : next 0x86 = out 0x86) (h6d : next 0x6D = out 0x6D)
    (h71a : next 0x71A = out 0x71A) (h71b : next 0x71B = out 0x71B) (h71c : next 0x71C = out 0x71C)
    (h71d : next 0x71D = out 0x71D) (h3a1 : next 0x3A1 = out 0x3A1)
    (h755 : next 0x755 = (pixelP out - leftL out).toUInt8)
    (h785 : out 0x785 = 0x10 → next 0x785 ≠ 0) : XInv next := by
  obtain ⟨hv, he, hp, hd, _⟩ := h
  have hP : pixelP next = pixelP out := by simp only [pixelP, h86, h6d]
  have hL : leftL next = leftL out := by simp only [leftL, h71a, h71c]
  have hR : edgeR next = edgeR out := by simp only [edgeR, h71b, h71d]
  refine ⟨by rw [h57]; exact hv, by rw [hR, hL]; exact he, by rw [h3a1]; exact hp, ?_, ?_⟩
  · rw [hP, hL]
    rcases hd with hd | ⟨hd, _⟩
    · exact Or.inl hd
    · exact Or.inr hd
  · intro h1 h2
    rw [hP, hL]
    rw [h755] at h1
    generalize pixelP out - leftL out = d at *
    rcases hd with hd | ⟨hd, ht⟩
    · constructor <;> revert h1 hd <;> bv_decide (config := { enums := false })
    · exact absurd h2 (h785 ht)

end Smb.Routine.HorizontalLimit
