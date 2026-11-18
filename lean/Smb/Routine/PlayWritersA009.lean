import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA009 : writersOk Smb.Abs.PlayParser.A009 = true := by native_decide

end Smb.Routine.PlayWriters
