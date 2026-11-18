import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA002 : writersOk Smb.Abs.PlayParser.A002 = true := by native_decide

end Smb.Routine.PlayWriters
