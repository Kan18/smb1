import Smb.Routine.WarpDestination
import Smb.Routine.InitializeAreaValues

/-!
The existing ROM proof of HandlePipeEntry ends at $DF4A. This bridge starts
only after the countdown has reached InitializeArea. Its `mid` equalities are
deliberate obligations on the intervening game updates, not assumed ROM facts.
-/

namespace Smb.Routine.RouteBridge
open Smb.Routine
open Smb.Routine.WarpDestination

private theorem area_keeps (sp : UInt8) (ram prg : UInt16 → UInt8)
    (i : UInt16) (hi : i = 0x750 ∨ i = 0x75c ∨ i = 0x75f ∨ i = 0x760 ∨
      i = 0x77f ∨ i = 0x7a7 ∨ i = 0x756) :
    initAreaRam sp ram prg i = ram i := by
  apply initAreaRam_keep
  · simp only [iaCleared]
    rcases hi with h | h | h | h | h | h | h <;> subst i <;> decide
  · simp only [iaTimer]
    rcases hi with h | h | h | h | h | h | h <;> subst i <;> decide
  · simp only [iaLate, iaLate7, iaStk]
    rcases hi with h | h | h | h | h | h | h <;> subst i <;> bv_decide

/-- The seven-byte random register and the three timer digits survive this
initializer itself. Later entrance code may reload the timer digits. -/
theorem area_rng_and_digits (sp : UInt8) (ram prg : UInt16 → UInt8)
    (i : UInt16)
    (hi : 0x7a7 ≤ i ∧ i ≤ 0x7ad ∨ 0x7f8 ≤ i ∧ i ≤ 0x7fa) :
    initAreaRam sp ram prg i = ram i := by
  apply initAreaRam_keep
  · simp only [iaCleared]
    rcases hi with h | h <;> bv_decide
  · simp only [iaTimer]
    rcases hi with h | h <;> bv_decide
  · simp only [iaLate, iaLate7, iaStk]
    rcases hi with h | h <;> bv_decide

/-- Area initialization keeps the warp destination, power, interval phase and
random seed, but clears the old warp selector and frame counter. -/
theorem area_boundary (sp : UInt8) (ram prg : UInt16 → UInt8) :
    initAreaRam sp ram prg 0x750 = ram 0x750 ∧
    initAreaRam sp ram prg 0x75c = ram 0x75c ∧
    initAreaRam sp ram prg 0x75f = ram 0x75f ∧
    initAreaRam sp ram prg 0x760 = ram 0x760 ∧
    initAreaRam sp ram prg 0x756 = ram 0x756 ∧
    initAreaRam sp ram prg 0x77f = ram 0x77f ∧
    initAreaRam sp ram prg 0x7a7 = ram 0x7a7 ∧
    initAreaRam sp ram prg 0x6d6 = 0 ∧
    initAreaRam sp ram prg 0x09 = 0 := by
  refine ⟨area_keeps sp ram prg _ (Or.inl rfl),
    area_keeps sp ram prg _ (Or.inr (Or.inl rfl)),
    area_keeps sp ram prg _ (Or.inr (Or.inr (Or.inl rfl))),
    area_keeps sp ram prg _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    area_keeps sp ram prg _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))),
    area_keeps sp ram prg _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
    area_keeps sp ram prg _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
    initAreaRam_clear sp ram prg _ (by decide) (by simp only [iaLate, iaLate7, iaStk]; bv_decide),
    initAreaRam_clear sp ram prg _ (by decide) (by simp only [iaLate, iaLate7, iaStk]; bv_decide)⟩

/-- Composes the proved pipe fragment with the proved area initializer once
the intervening countdown is known to preserve the destination bytes. -/
theorem warp_world_after_area_init
    (sp spArea : UInt8) (before mid : UInt16 → UInt8) (t : Plain)
    (hpipe : Summary sp before actualPrg t)
    (hmid : mid 0x75f = t.ram 0x75f) :
    initAreaRam spArea mid actualPrg 0x75f =
      (bif activeWarp before then worldAt actualPrg (tableIndex (before 0x6d6) (before 0x86))
        else before 0x75f) := by
  rw [(area_boundary spArea mid actualPrg).2.2.1, hmid]
  exact hpipe.2.2.2.2.1

/-- The pipe-selected level is likewise carried to area initialization;
normal later stream parsing may still change the area pointer. -/
theorem warp_level_after_area_init
    (sp spArea : UInt8) (before mid : UInt16 → UInt8) (t : Plain)
    (hpipe : Summary sp before actualPrg t)
    (hmid : mid 0x75c = t.ram 0x75c) :
    initAreaRam spArea mid actualPrg 0x75c =
      (bif activeWarp before then 0 else before 0x75c) := by
  rw [(area_boundary spArea mid actualPrg).2.1, hmid]
  exact hpipe.2.2.2.2.2.2.1

end Smb.Routine.RouteBridge
