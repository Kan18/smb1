import Smb.Game
import Smb.Abs.FrameData

/-! The checker accepts the table for the NMI handler up to the game logic. -/
namespace Smb.Routine.Frame

theorem linkedH : Smb.Abs.Frame.linkedH Smb.prg = true := by native_decide

end Smb.Routine.Frame
