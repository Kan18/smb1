import Smb.Game
import Smb.Abs.FrameData

/-! The checker accepts the table for the end of the handler, the idle loop, and the next NMI up to `$808F`. -/
namespace Smb.Routine.Frame

theorem linkedZ : Smb.Abs.Frame.linkedZ Smb.prg = true := by native_decide

end Smb.Routine.Frame
