import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA005 : writersOk Smb.Abs.PlayParser.A005 = true := by native_decide

end Smb.Routine.PlayWriters
