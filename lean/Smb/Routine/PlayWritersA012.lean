import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA012 : writersOk Smb.Abs.PlayParser.A012 = true := by native_decide

end Smb.Routine.PlayWriters
