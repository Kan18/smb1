import Smb.Game
import Smb.Abs.LaunchData

/-! The checker accepts the table for the end of the handler, the idle loop, and the next NMI up to `$808F`, during the launch. -/
namespace Smb.Routine.LaunchPhase

theorem linkedZ : Smb.Abs.LaunchPhase.linkedZ Smb.prg = true := by native_decide

end Smb.Routine.LaunchPhase
