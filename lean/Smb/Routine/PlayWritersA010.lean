import Smb.Routine.PlayWritersDefs
import Smb.PlayParserData

namespace Smb.Routine.PlayWriters

theorem okA010 : writersOk Smb.Abs.PlayParser.A010 = true := by native_decide

end Smb.Routine.PlayWriters
