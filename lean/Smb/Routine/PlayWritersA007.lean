import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA007 : writersOk Smb.Abs.PlayParser.A007 = true := by native_decide

end Smb.Routine.PlayWriters
