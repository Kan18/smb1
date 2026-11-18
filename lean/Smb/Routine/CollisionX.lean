import Smb.Routine.HorizontalLimit
import Smb.Routine.Impede

/-!
# Composing the collision code's horizontal effect

`HorizontalLimit.BgX` is what the collision code may do to Mario's horizontal state: nothing, or one push with the
speed zeroed. These put it together from pieces: a stretch that keeps the horizontal bytes, followed by one `BgX`
step, is a `BgX` step; and `ImpedePlayerMove` on any RAM is one.
-/
namespace Smb.Routine.HorizontalLimit

/-- A stretch that keeps the bytes `BgX` reads, then a `BgX` step. -/
theorem bgX_of_kept (ram mid out : UInt16 → UInt8) (h400 : mid 0x400 = ram 0x400) (h86 : mid 0x86 = ram 0x86)
    (h6d : mid 0x6D = ram 0x6D) (h57 : mid 0x57 = ram 0x57) (h : BgX mid out) : BgX ram out := by
  simp only [BgX, pixelP, h400, h86, h6d, h57] at h ⊢
  exact h

/-- Keeping the bytes is a `BgX` step. -/
theorem bgX_refl (ram out : UInt16 → UInt8) (h400 : out 0x400 = ram 0x400) (h86 : out 0x86 = ram 0x86)
    (h6d : out 0x6D = ram 0x6D) (h57 : out 0x57 = ram 0x57) : BgX ram out := by
  refine ⟨h400, Or.inl ⟨?_, h57⟩⟩
  simp only [pixelP, h86, h6d]

/-- `ImpedePlayerMove`, whichever side `$00` names. -/
theorem impede_bgX (ram : UInt16 → UInt8) : BgX ram (impedeRam (ram 0) ram) := by
  simp only [BgX, impedeRam, impedeInto, pixelP, pos16]
  bv_decide (config := { enums := false })

end Smb.Routine.HorizontalLimit
