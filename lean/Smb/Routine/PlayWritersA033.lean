import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA033 : writersOk Smb.Abs.PlayParser.A033 = true := by native_decide

end Smb.Routine.PlayWriters
