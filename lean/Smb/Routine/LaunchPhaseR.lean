import Smb.Game
import Smb.Abs.LaunchData

/-! The checker accepts the table for after `PlayerCtrlRoutine`, up to the enemy loop, during the launch. -/
namespace Smb.Routine.LaunchPhase

theorem linkedR : Smb.Abs.LaunchPhase.linkedR Smb.prg = true := by native_decide

end Smb.Routine.LaunchPhase
