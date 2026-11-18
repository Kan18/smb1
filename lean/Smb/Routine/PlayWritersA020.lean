import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA020 : writersOk Smb.Abs.PlayParser.A020 = true := by native_decide

end Smb.Routine.PlayWriters
