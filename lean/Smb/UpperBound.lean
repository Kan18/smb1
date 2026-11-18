import Smb.Game
import Smb.Tas

/-!
# Upper bound: SMB can be beaten in 17,866 frames

Under the model in `Smb.Nes` (from power-on with a soft reset before frame 0, one
controller-1 byte per frame, controller 2 idle, no further resets), HappyLee's TAS
(TASVideos #1715) beats the game: after its first 17,866 frames `finalVictory` is true
(victory mode in World 8-4), and none of the model's unsupported-behavior guards fired.
This is not a hardware-equivalence theorem.

The witness removes the original movie's first idle frame for this model's startup
clock origin. This is not a gameplay improvement. In zero-indexed terms victory is
observed at the end of frame 17,865. The first frame is a partial PPU frame.

## Trust

The proofs use `native_decide`: the statement is decided by running the compiled model, so
they rely on the compiled evaluation as well as Lean's kernel. `#print axioms` lists
the generated `native_decide` axioms for the replay and input length. The replay
takes about 5 × 10⁸ emulated CPU cycles.
-/
namespace Smb

instance (inputs : List UInt8) : Decidable (beatenBy inputs) := by
  unfold beatenBy; exact inferInstance

/-- The first 17,866 frames of the TAS beat the game. -/
theorem tas_beats_game : beatenBy (tasInputs.take 17866) := by native_decide

theorem tas_prefix_length : (tasInputs.take 17866).length = 17866 := by native_decide

/-- **Upper bound.** Some input sequence of 17,866 frames beats the game. -/
theorem upper_bound : ∃ inputs : List UInt8, inputs.length = 17866 ∧ beatenBy inputs :=
  ⟨tasInputs.take 17866, tas_prefix_length, tas_beats_game⟩

end Smb
