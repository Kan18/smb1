import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA001 : writersOk Smb.Abs.PlayParser.A001 = true := by native_decide

end Smb.Routine.PlayWriters
