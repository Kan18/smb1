import Smb.Routine.PlayParserA000
import Smb.Routine.PlayParserA001
import Smb.Routine.PlayParserA002
import Smb.Routine.PlayParserA003
import Smb.Routine.PlayParserA004
import Smb.Routine.PlayParserA005
import Smb.Routine.PlayParserA006
import Smb.Routine.PlayParserA007
import Smb.Routine.PlayParserA008
import Smb.Routine.PlayParserA009
import Smb.Routine.PlayParserA010
import Smb.Routine.PlayParserA011
import Smb.Routine.PlayParserA012
import Smb.Routine.PlayParserA013
import Smb.Routine.PlayParserA014
import Smb.Routine.PlayParserA015
import Smb.Routine.PlayParserA016
import Smb.Routine.PlayParserA017
import Smb.Routine.PlayParserA018
import Smb.Routine.PlayParserA019
import Smb.Routine.PlayParserA020
import Smb.Routine.PlayParserA021
import Smb.Routine.PlayParserA022
import Smb.Routine.PlayParserA023
import Smb.Routine.PlayParserA024
import Smb.Routine.PlayParserA025
import Smb.Routine.PlayParserA026
import Smb.Routine.PlayParserA027
import Smb.Routine.PlayParserA028
import Smb.Routine.PlayParserA029
import Smb.Routine.PlayParserA030
import Smb.Routine.PlayParserA031
import Smb.Routine.PlayParserA032
import Smb.Routine.PlayParserA033
import Smb.Routine.PlayParserA034
import Smb.Routine.PlayParserA035
import Smb.Routine.PlayParserA036
import Smb.Routine.PlayParserA037
import Smb.Routine.PlayParserA038
import Smb.Routine.PlayParserA039
import Smb.Routine.PlayParserA040
import Smb.Routine.PlayParserA041

/-! Every listed chunk passes its checker. This is not a whole-frame or level theorem. -/
namespace Smb.Routine.PlayParser
open Smb.Abs.PlayParser

theorem checked : chunks.all (accepted Smb.prg) = true := by
  simp only [chunks, List.all_cons, List.all_nil, checkedA000, checkedA001, checkedA002, checkedA003, checkedA004, checkedA005, checkedA006, checkedA007, checkedA008, checkedA009, checkedA010, checkedA011, checkedA012, checkedA013, checkedA014, checkedA015, checkedA016, checkedA017, checkedA018, checkedA019, checkedA020, checkedA021, checkedA022, checkedA023, checkedA024, checkedA025, checkedA026, checkedA027, checkedA028, checkedA029, checkedA030, checkedA031, checkedA032, checkedA033, checkedA034, checkedA035, checkedA036, checkedA037, checkedA038, checkedA039, checkedA040, checkedA041, Bool.and_self]

end Smb.Routine.PlayParser
