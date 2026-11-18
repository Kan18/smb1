import Smb.Game
import Smb.Abs.LaunchData

/-! The checker accepts the table for the enemy loop, during the launch. -/
namespace Smb.Routine.LaunchPhase

theorem linkedE : Smb.Abs.LaunchPhase.linkedE Smb.prg = true := by native_decide

end Smb.Routine.LaunchPhase
