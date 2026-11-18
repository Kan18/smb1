import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
One write of `DigitsMathRoutine`. The machine checks sign before decimal
carry, so every value reaching `StoreNewD` is below `$8f` even if the
modifier or old digit is not decimal. This is weaker than a BCD invariant
but sufficient for the proposed `$8f` source exclusion.
-/
namespace Smb.Buffer.Digits.DigitMath
open Smb Smb.Routine

def mainCode : List UInt8 :=
  smbPrg% 0x8F68 16

def carryCode : List UInt8 :=
  smbPrg% 0x8F87 16

def copyCode : List UInt8 :=
  smbPrg% 0x8F47 6

def rom (addr : UInt16) : UInt8 := Smb.prg.get! (addr &&& 0x7fff).toNat

theorem mainCode_in_rom : CodeAt rom 0x0f68 mainCode :=
  codeAt_of_matches _ _ _ (by native_decide)
theorem carryCode_in_rom : CodeAt rom 0x0f87 carryCode :=
  codeAt_of_matches _ _ _ (by native_decide)
theorem copyCode_in_rom : CodeAt rom 0x0f47 copyCode :=
  codeAt_of_matches _ _ _ (by native_decide)

def digitResult (modifier old : UInt8) : UInt8 :=
  let sum := modifier + old
  if sum &&& 0x80 ≠ 0 then 9
  else if sum < 10 then sum
  else sum - 10

theorem digitResult_below_8f (modifier old : UInt8) :
    digitResult modifier old ≤ 0x75 := by
  unfold digitResult
  bv_decide

/-- A decimal 0..9 conclusion really does need a modifier bound. This is a
local arithmetic example, not a legal-play input. -/
theorem arbitrary_modifier_can_make_nondecimal :
    digitResult 0x7f 0 = 0x75 := by decide

set_option maxHeartbeats 3000000 in
theorem one_store_below_8f
    (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hmain : CodeAt prg 0x0f68 mainCode)
    (hcarry : CodeAt prg 0x0f87 carryCode)
    (hI : p &&& 4 ≠ 0) (hy : y ≤ 35) :
    let s : Plain := ⟨⟨0x8f68, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x8f78 16).run s).2
    t.bad = false ∧ t.regs.pc = 0x8f78 ∧
      t.ram (0x7d7 + y.toUInt16) ≤ 0x75 := by
  dsimp only
  simp only [CodeAt, mainCode, carryCode, UInt16.reduceAdd] at hmain hcarry
  generalize hr : ((CPU.runTo (σ := Plain) 0x8f78 16).run
    ⟨⟨0x8f68, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hr [hmain, hcarry, hi, hy]
  all_goals
    intros
    clear hmain hcarry hi
    simp_all
    try bv_decide

set_option maxHeartbeats 2000000 in
/-- The `OutputNumbers` digit copy preserves the weaker `$75` bound.
Its source-index bound is supplied by the controlled selector table. -/
theorem copied_digit_below_8f
    (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x0f47 copyCode)
    (hI : p &&& 4 ≠ 0) (hy : y ≤ 35)
    (hd : ram (0x7d7 + y.toUInt16) ≤ 0x75) :
    let s : Plain := ⟨⟨0x8f47, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x8f4d 3).run s).2
    t.bad = false ∧ t.regs.pc = 0x8f4d ∧
      t.ram (0x304 + x.toUInt16) ≤ 0x75 := by
  dsimp only
  simp only [CodeAt, copyCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x8f4d 3).run
    ⟨⟨0x8f47, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  have haddr : (0x7d7 + y.toUInt16) &&& 0x7ff =
      0x7d7 + y.toUInt16 := by bv_decide
  sym_run hr [hc, hi, hy, hd, haddr]
  all_goals
    intros
    clear hc hi
    simp_all
    try bv_decide

/-- Full-NES version of the one-iteration range bound.  The routine fragment
uses only RAM and ROM bus accesses, so `refine_runTo` applies. -/
theorem one_store_below_8f_nes (s : NES)
    (hq : s.Quiet) (hprg : s.prg = Smb.prg)
    (hpc : s.pc = 0x8f68) (hI : s.p &&& 4 ≠ 0)
    (hy : s.y ≤ 35) :
    let t := ((CPU.runTo (σ := NES) 0x8f78 16).run s).2
    t.pc = 0x8f78 ∧
      ramAt t (0x7d7 + s.y.toUInt16) ≤ 0x75 := by
  intro t
  have ht : s.toPlain = ⟨⟨0x8f68, s.a, s.x, s.y, s.s, s.p⟩,
      ramAt s, fun a => s.prg.get! (a &&& 0x7fff).toNat,
      s.cyc, false⟩ := by
    simp only [NES.toPlain, hpc]
    rfl
  have hm : CodeAt (fun a => s.prg.get! (a &&& 0x7fff).toNat)
      0x0f68 mainCode := by
    rw [hprg]
    exact mainCode_in_rom
  have hc : CodeAt (fun a => s.prg.get! (a &&& 0x7fff).toNat)
      0x0f87 carryCode := by
    rw [hprg]
    exact carryCode_in_rom
  have hs := one_store_below_8f s.a s.x s.y s.s s.p
    (ramAt s) _ s.cyc hm hc hI hy
  rw [← ht] at hs
  obtain ⟨hbad, hpc', hbound⟩ := hs
  have hr := refine_runTo s hq 0x8f78 16 hbad
  have haddr : (0x7d7 : UInt16) + s.y.toUInt16 < 0x800 := by
    revert hy
    bv_decide
  refine ⟨(congrArg Regs.pc hr.regs).trans hpc', ?_⟩
  rw [ramAt_of_rel hr, and7ff_of_lt _ haddr]
  exact hbound

/-- Full-NES copy bound for any source digit already below `$76`. -/
theorem copied_digit_below_8f_nes (s : NES)
    (hq : s.Quiet) (hprg : s.prg = Smb.prg)
    (hpc : s.pc = 0x8f47) (hI : s.p &&& 4 ≠ 0)
    (hy : s.y ≤ 35)
    (hsource : ramAt s (0x7d7 + s.y.toUInt16) ≤ 0x75) :
    let t := ((CPU.runTo (σ := NES) 0x8f4d 3).run s).2
    t.pc = 0x8f4d ∧
      ramAt t (0x304 + s.x.toUInt16) ≤ 0x75 := by
  intro t
  have ht : s.toPlain = ⟨⟨0x8f47, s.a, s.x, s.y, s.s, s.p⟩,
      ramAt s, fun a => s.prg.get! (a &&& 0x7fff).toNat,
      s.cyc, false⟩ := by
    simp only [NES.toPlain, hpc]
    rfl
  have hc : CodeAt (fun a => s.prg.get! (a &&& 0x7fff).toNat)
      0x0f47 copyCode := by
    rw [hprg]
    exact copyCode_in_rom
  have hs := copied_digit_below_8f s.a s.x s.y s.s s.p
    (ramAt s) _ s.cyc hc hI hy hsource
  rw [← ht] at hs
  obtain ⟨hbad, hpc', hbound⟩ := hs
  have hr := refine_runTo s hq 0x8f4d 3 hbad
  have haddr : (0x304 : UInt16) + s.x.toUInt16 < 0x800 := by
    bv_decide
  refine ⟨(congrArg Regs.pc hr.regs).trans hpc', ?_⟩
  rw [ramAt_of_rel hr, and7ff_of_lt _ haddr]
  exact hbound

end Smb.Buffer.Digits.DigitMath
