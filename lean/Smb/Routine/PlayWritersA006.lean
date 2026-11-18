import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA006 : writersOk Smb.Abs.PlayParser.A006 = true := by native_decide

end Smb.Routine.PlayWriters
