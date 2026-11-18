import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA035 : writersOk Smb.Abs.PlayParser.A035 = true := by native_decide

end Smb.Routine.PlayWriters
