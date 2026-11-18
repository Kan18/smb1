import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA004 : writersOk Smb.Abs.PlayParser.A004 = true := by native_decide

end Smb.Routine.PlayWriters
