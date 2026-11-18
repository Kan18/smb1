import Smb.Routine.PlayWriters
import Smb.Routine.PlayWritersH
import Smb.Routine.PlayWritersP
import Smb.Routine.PlayWritersFront
import Smb.Routine.PlayWritersE0
import Smb.Routine.PlayWritersM0
import Smb.Routine.PlayWritersE1
import Smb.Routine.PlayWritersM1
import Smb.Routine.PlayWritersE2
import Smb.Routine.PlayWritersM2
import Smb.Routine.PlayWritersE3
import Smb.Routine.PlayWritersM3
import Smb.Routine.PlayWritersE4
import Smb.Routine.PlayWritersM4
import Smb.Routine.PlayWritersE5
import Smb.Routine.PlayWritersM5
import Smb.Routine.PlayWritersT
import Smb.Routine.PlayWritersZ
import Smb.Routine.PlayWritersA000
import Smb.Routine.PlayWritersA001
import Smb.Routine.PlayWritersA002
import Smb.Routine.PlayWritersA003
import Smb.Routine.PlayWritersA004
import Smb.Routine.PlayWritersA005
import Smb.Routine.PlayWritersA006
import Smb.Routine.PlayWritersA007
import Smb.Routine.PlayWritersA008
import Smb.Routine.PlayWritersA009
import Smb.Routine.PlayWritersA010
import Smb.Routine.PlayWritersA011
import Smb.Routine.PlayWritersA012
import Smb.Routine.PlayWritersA013
import Smb.Routine.PlayWritersA014
import Smb.Routine.PlayWritersA015
import Smb.Routine.PlayWritersA016
import Smb.Routine.PlayWritersA017
import Smb.Routine.PlayWritersA018
import Smb.Routine.PlayWritersA019
import Smb.Routine.PlayWritersA020
import Smb.Routine.PlayWritersA021
import Smb.Routine.PlayWritersA022
import Smb.Routine.PlayWritersA023
import Smb.Routine.PlayWritersA024
import Smb.Routine.PlayWritersA025
import Smb.Routine.PlayWritersA026
import Smb.Routine.PlayWritersA027
import Smb.Routine.PlayWritersA028
import Smb.Routine.PlayWritersA029
import Smb.Routine.PlayWritersA030
import Smb.Routine.PlayWritersA031
import Smb.Routine.PlayWritersA032
import Smb.Routine.PlayWritersA033
import Smb.Routine.PlayWritersA034
import Smb.Routine.PlayWritersA035
import Smb.Routine.PlayWritersA036
import Smb.Routine.PlayWritersA037
import Smb.Routine.PlayWritersA038
import Smb.Routine.PlayWritersA039
import Smb.Routine.PlayWritersA040
import Smb.Routine.PlayWritersA041

/-!
# Writers of buffer scheduling and scroll state during normal play

`writers_all` combines the region checks. `step_writers` then restricts changes
to the listed instruction addresses when the normal-play invariant and the
support and buffer conditions hold. Building this optional target with
`lake build Smb.Routine.PlayWritersAll` recomputes the region tables.
-/
namespace Smb.Routine.PlayWriters
open Smb NES Smb.Abs Smb.Routine Smb.Routine.FrameGuard Smb.Routine.PlayCycle

theorem writers_all : ∀ c ∈ configs, writersOk c = true := by
  have h : configs.all writersOk = true := by
    simp only [configs, PlaySavedHandoffs.normalConfigs, PlayParser.chunks, List.cons_append, List.nil_append,
      List.all_cons, List.all_nil, okH, okP, okFront, okE0, okM0, okE1, okM1, okE2, okM2, okE3, okM3, okE4, okM4, okE5, okM5, okT, okZ, okA000, okA001, okA002, okA003, okA004, okA005, okA006, okA007, okA008, okA009, okA010, okA011, okA012, okA013, okA014, okA015, okA016, okA017, okA018, okA019, okA020, okA021, okA022, okA023, okA024, okA025, okA026, okA027, okA028, okA029, okA030, okA031, okA032, okA033, okA034, okA035, okA036, okA037, okA038, okA039, okA040, okA041, Bool.and_self]
  exact List.all_eq_true.mp h

/-- **A step of normal play changes a group's cell only at that cell's writers.** -/
theorem step_writers {k : Group} (hk : k ∈ groups) {s : NES} (h : CycleInv s) (hd : stop s.pc = false)
    (hus : s.unmodelled = false) (hu : (CPU.step.run s).2.unmodelled = false) (hcl : CleanIf (CPU.step.run s).2)
    (hS : k.writers.contains s.pc = false) (i : UInt16) (hi : k.cells i = true) :
    (CPU.step.run s).2.ram.get! i.toNat = s.ram.get! i.toNat := by
  have hgr : k = addrCtrl ∨ k = parserTask ∨ k = floateyTimers ∨ k = gameTimerCtrl ∨ k = frameCounter ∨
      k = scrollPos ∨ k = sideTimer := by
    simpa [groups] using hk
  refine cycle_step_writers writers_all hk ?_ ?_ h hd hus hu hcl hS i hi
  · intro j hj
    rcases hgr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [addrCtrl, parserTask, floateyTimers, gameTimerCtrl, frameCounter, scrollPos, sideTimer] at hj <;>
      first | (subst hj; decide) | bv_decide
  · rcases hgr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Smb.Routine.PlayWriters
