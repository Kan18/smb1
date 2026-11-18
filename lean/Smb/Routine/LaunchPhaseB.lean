import Smb.Game
import Smb.Abs.LaunchData

/-! The checker accepts the table for the end of the engine, during the launch. -/
namespace Smb.Routine.LaunchPhase

theorem linkedB : Smb.Abs.LaunchPhase.linkedB Smb.prg = true := by native_decide

end Smb.Routine.LaunchPhase
