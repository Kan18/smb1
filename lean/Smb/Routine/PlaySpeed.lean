import Smb.Game
import Smb.PlaySpeedData

/-! A checked general player-region table, not a whole-frame invariant. -/
namespace Smb.Routine.PlaySpeed

theorem accepted : Smb.Abs.PlaySpeed.accepted Smb.prg = true := by native_decide

end Smb.Routine.PlaySpeed
