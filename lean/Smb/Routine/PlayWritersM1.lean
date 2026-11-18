import Smb.Routine.PlayWritersDefs
import Smb.PlayEnemyData

namespace Smb.Routine.PlayWriters

theorem okM1 : writersOk Smb.Abs.PlayEnemy.M1 = true := by native_decide

end Smb.Routine.PlayWriters
