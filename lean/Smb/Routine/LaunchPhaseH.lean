import Smb.Game
import Smb.Abs.LaunchData

/-! The checker accepts the table for the NMI handler up to the game logic, during the launch. -/
namespace Smb.Routine.LaunchPhase

theorem linkedH : Smb.Abs.LaunchPhase.linkedH Smb.prg = true := by native_decide

end Smb.Routine.LaunchPhase
