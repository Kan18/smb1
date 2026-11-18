import Smb.Game
import Smb.Abs.LaunchData

/-! The checker accepts the table for `SaveAB`, during the launch. -/
namespace Smb.Routine.LaunchPhase

theorem linkedA : Smb.Abs.LaunchPhase.linkedA Smb.prg = true := by native_decide

end Smb.Routine.LaunchPhase
