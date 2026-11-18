import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA040 : writersOk Smb.Abs.PlayParser.A040 = true := by native_decide

end Smb.Routine.PlayWriters
