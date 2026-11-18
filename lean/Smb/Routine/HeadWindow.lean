import Smb.Routine.FloorClip

/-!
# Head window (pure arithmetic), the upward companion of `floor_window` / `floor_skip_iff`.

`PlayerBGCollision`'s head check nullifies a rising Mario only when `Player_Y_Position & $0F ≥ 4`, on
the frames his head probe (`Y + a`, `a = 4` big, `a = 2` big swimming, `a = $12` small or crouching) is in a
non-empty metatile. These theorems say when the first frame in a new row can have `Y & $0F < 4`, by the step:
- big: only if the step is at least 9 pixels (`head_window_big`);
- small, crouching, big swimming: only if the step is at least 11 (`head_window_small`, `head_window_swim`).
The hypotheses include a row change and old Y in $40..$E0. These arithmetic
lemmas do not cover horizontal entry into another cell in the same row, nor do
they bound all sources of vertical repositioning in the game.
-/
namespace Smb.Routine

/-- The head probe at `Y + a` changes metatile row between `y` and `y'`. -/
def headRowChanges (a y y' : UInt8) : Bool := (y + a) >>> 4 != (y' + a) >>> 4

/-- Rising by `s` pixels, big Mario: the first frame in a new row has `Y & $0F ≥ 4` when `s ≤ 8`. -/
theorem head_window_big (y s : UInt8) (hs : s ≤ 8) (hn : s ≠ 0) (hy : 0x40 ≤ y) (ht : y ≤ 0xE0)
    (hrow : headRowChanges 4 y (y - s) = true) : 4 ≤ (y - s) &&& 0x0F := by
  simp only [headRowChanges, bne] at *
  bv_decide

/-- Same for the probe at `Y + $12` (small or crouching) when `s ≤ 10`. -/
theorem head_window_small (y s : UInt8) (hs : s ≤ 10) (hn : s ≠ 0) (hy : 0x40 ≤ y) (ht : y ≤ 0xE0)
    (hrow : headRowChanges 0x12 y (y - s) = true) : 4 ≤ (y - s) &&& 0x0F := by
  simp only [headRowChanges, bne] at *
  bv_decide

/-- Same for the probe at `Y + 2` (big swimming) when `s ≤ 10`. -/
theorem head_window_swim (y s : UInt8) (hs : s ≤ 10) (hn : s ≠ 0) (hy : 0x40 ≤ y) (ht : y ≤ 0xE0)
    (hrow : headRowChanges 2 y (y - s) = true) : 4 ≤ (y - s) &&& 0x0F := by
  simp only [headRowChanges, bne] at *
  bv_decide

/-- The bounds are sharp: big at step 9, small at step 11. -/
example : headRowChanges 4 0x6C (0x6C - 9) = true ∧ (0x6C - 9 : UInt8) &&& 0x0F < 4 := by decide
example : headRowChanges 0x12 0x5E (0x5E - 11) = true ∧ (0x5E - 11 : UInt8) &&& 0x0F < 4 := by decide

/-- From `gravityVel`-free reasoning: a velocity byte pair with speed `≥ $F8` moves `Y` up at most 8. -/
theorem rise_le_8 (pos : UInt32) (vel : UInt16) (hv : 0xF800 ≤ vel) :
    (posY pos - posY (nextPos pos vel)) ≤ 8 ∨ posY pos < posY (nextPos pos vel) ∨ posY pos = posY (nextPos pos vel) := by
  simp only [posY, nextPos, sext16] at *
  bv_decide

end Smb.Routine

#print axioms Smb.Routine.head_window_big
#print axioms Smb.Routine.head_window_small
#print axioms Smb.Routine.head_window_swim
#print axioms Smb.Routine.rise_le_8
