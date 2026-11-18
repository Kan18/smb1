import Smb.Game
import Smb.PlayPlayerData

/-! A checked general player-region table, not a whole-frame invariant. -/
namespace Smb.Routine.PlayPlayer

theorem accepted : Smb.Abs.PlayPlayer.accepted Smb.prg = true := by native_decide

end Smb.Routine.PlayPlayer
