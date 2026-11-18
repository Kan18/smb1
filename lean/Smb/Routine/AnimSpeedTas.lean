import Smb.Routine.AnimSpeed
import Smb.Game
import Smb.Tas

/-!
# The skid stop in play

From the TAS's first frame of walking in 1-1 (frame 196 of `tasInputs`), hold Right for three
frames (X speed 3), then press one other button. Run on the full NES model:

| next frame's input | X speed |
|---|---|
| nothing | 2 (friction) |
| Down, B, Up or Select alone | 0 (`skidStops`) |
| Left | −1 (skid, then acceleration) |

(Controller byte of this model: bit 0 A, 1 B, 2 Select, 3 Start, 4 Up, 5 Down, 6 Left, 7 Right.)
-/
namespace Smb.Routine

def skidPrefix : List UInt8 := tasInputs.take 196 ++ [0x80, 0x80, 0x80]

def speedAfter (b : UInt8) : UInt8 :=
  (NES.runFrames (skidPrefix ++ [b]) initial).ram.get! 0x57

theorem skid_stop_in_play :
    speedAfter 0x00 = 2 ∧ speedAfter 0x20 = 0 ∧ speedAfter 0x02 = 0 ∧ speedAfter 0x10 = 0 ∧
      speedAfter 0x04 = 0 ∧ speedAfter 0x40 = 0xFF := by
  native_decide

end Smb.Routine
