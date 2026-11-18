import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA023 : writersOk Smb.Abs.PlayParser.A023 = true := by native_decide

end Smb.Routine.PlayWriters
