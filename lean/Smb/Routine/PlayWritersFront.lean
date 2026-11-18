import Smb.Routine.PlayWritersDefs
import Smb.PlayEnemyData

namespace Smb.Routine.PlayWriters

theorem okFront : writersOk Smb.Abs.PlayEnemy.Front = true := by native_decide

end Smb.Routine.PlayWriters
