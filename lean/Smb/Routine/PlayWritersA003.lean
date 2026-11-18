import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA003 : writersOk Smb.Abs.PlayParser.A003 = true := by native_decide

end Smb.Routine.PlayWriters
