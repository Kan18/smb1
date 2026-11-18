import Smb.Routine.Landing
import Smb.Routine.ImposeGravity

/-!
# When can Mario fall through a floor?

Combines three proved routine facts:
- the vertical position moves by the velocity from before this frame's gravity
  (`imposeGravity`: 16.8 position += sign-extended 8.8 velocity);
- the velocity after gravity `$90` and maximum 4 is at most `$050F` (`gravityVel_le_050F`);
- Mario lands only if, in the first frame his feet are in a metatile row, the row offset
  `Player_Y_Position & $0F` is below 5 (`chkFootMTile_reach`; otherwise he is pushed
  sideways and keeps falling).

Feet enter a new row (the probe is at `Y + $20`) exactly when the position byte crosses a
multiple of 16. The theorems below decide when that crossing can skip offsets 0–4:
- below speed 5 it never can (`floor_window`);
- at speed 5.s (s ≤ 15 is all gravity allows) it can exactly when the position is at offset
  15 of the row above with sub-pixel `≥ 256 − s` (`floor_skip_iff`), i.e. within 15
  sub-pixels: the "precise down to 15 subpixels" requirement of the 1-2 vine floor clip.

Whether jumps, falls, bounces and vines can produce that state is the remaining (number
theory) question; see NOTES.
-/
namespace Smb.Routine

/-- Position after one frame (`imposeGravity`'s position update). -/
def nextPos (pos : UInt32) (vel : UInt16) : UInt32 := (pos + sext16 vel) &&& 0xFFFFFF

/-- `Player_Y_Position`, the middle byte of the 16.8 position. -/
def posY (pos : UInt32) : UInt8 := (pos >>> 8).toUInt8

/-- The feet's metatile row changes (the foot probe is 32 pixels below `Y`). -/
def entersRow (pos : UInt32) (vel : UInt16) : Bool :=
  (posY pos + 0x20) >>> 4 != (posY (nextPos pos vel) + 0x20) >>> 4

/-- Gravity at most `$90` with maximum 4 never takes a velocity within the maximum
(`withinMax`: speed below 4, or 4 with fraction below `$80`, which every call with `A = 0`
leaves behind when gravity is at most `$80`) above `$050F`. (`$04FF` + `$80` would give
`$057F`, but `$04FF` is not within the maximum.) -/
theorem gravityVel_le_050F (down : UInt8) (v : UInt16) (hd : down ≤ 0x90)
    (hlow : (v >>> 8).toUInt8 + 0x40 < 0x80) (hv : withinMax 4 v = true) :
    gravityVel 0 down 0 4 v < 0x8000 → gravityVel 0 down 0 4 v ≤ 0x050F := by
  simp only [gravityVel, withinMax] at *
  bv_decide

/-- Falling at less than speed 5, the first frame in a new row always has offset 0–4.
Landing additionally requires the actual collision dispatch to reach its landing test
with a selected landable metatile; a coin or another early exit can bypass that test. -/
theorem floor_window (pos : UInt32) (vel : UInt16) (hv : vel < 0x0500)
    (hrow : entersRow pos vel = true) :
    posY (nextPos pos vel) &&& 0x0F < 5 := by
  simp only [entersRow, posY, nextPos, sext16, bne] at *
  bv_decide

/-- At speed 5.s (as gravity allows), the feet skip offsets 0–4 of the new row exactly when
the position is at offset 15 of the row above and the sub-pixel carries. -/
theorem floor_skip_iff (pos : UInt32) (vel : UInt16) (hv : 0x0500 ≤ vel ∧ vel ≤ 0x050F) :
    (entersRow pos vel = true ∧ 5 ≤ posY (nextPos pos vel) &&& 0x0F) ↔
      (posY pos &&& 0x0F = 0x0F ∧ 0x100 ≤ (pos &&& 0xFF) + (vel &&& 0xFF).toUInt32) := by
  simp only [entersRow, posY, nextPos, sext16, bne]
  bv_decide

/-- The clip state exists: offset 15, sub-pixel `$F8`, velocity `$0508` (speed 5, sub-speed 8:
the only land value with sub-speed a multiple of 8 that carries). -/
example : entersRow 0x01_2F_F8 0x0508 = true ∧ posY (nextPos 0x01_2F_F8 0x0508) &&& 0x0F = 5 := by
  decide

end Smb.Routine
