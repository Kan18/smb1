import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA021 : writersOk Smb.Abs.PlayParser.A021 = true := by native_decide

end Smb.Routine.PlayWriters
