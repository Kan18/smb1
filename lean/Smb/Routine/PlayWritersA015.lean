import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA015 : writersOk Smb.Abs.PlayParser.A015 = true := by native_decide

end Smb.Routine.PlayWriters
