import Smb.Game
import Smb.Abs.LaunchData

/-! The checker accepts the table for the engine after the enemy loop, during the launch. -/
namespace Smb.Routine.LaunchPhase

theorem linkedT : Smb.Abs.LaunchPhase.linkedT Smb.prg = true := by native_decide

end Smb.Routine.LaunchPhase
