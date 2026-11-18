import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA025 : writersOk Smb.Abs.PlayParser.A025 = true := by native_decide

end Smb.Routine.PlayWriters
