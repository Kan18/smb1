import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA022 : writersOk Smb.Abs.PlayParser.A022 = true := by native_decide

end Smb.Routine.PlayWriters
