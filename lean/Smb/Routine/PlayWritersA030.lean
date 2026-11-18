import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA030 : writersOk Smb.Abs.PlayParser.A030 = true := by native_decide

end Smb.Routine.PlayWriters
