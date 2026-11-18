import Smb.Game
import Smb.PlayParserData

namespace Smb.Routine.PlayParser
open Smb.Abs.PlayParser

theorem checkedA003 : accepted Smb.prg A003 = true := by native_decide

end Smb.Routine.PlayParser
