import Smb.Game
import Smb.PlayEnemyData

namespace Smb.Routine.PlayEnemy
open Smb.Abs.PlayEnemy

theorem checkedFront : acceptedFront Smb.prg = true := by native_decide

end Smb.Routine.PlayEnemy
