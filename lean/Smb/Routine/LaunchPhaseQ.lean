import Smb.Game
import Smb.Abs.LaunchData

/-! The checker accepts the table for the game mode dispatch up to `PlayerCtrlRoutine`, during the launch. -/
namespace Smb.Routine.LaunchPhase

theorem linkedQ : Smb.Abs.LaunchPhase.linkedQ Smb.prg = true := by native_decide

end Smb.Routine.LaunchPhase
