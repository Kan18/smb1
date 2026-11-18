import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# Warp-pipe selection for every selector byte

The bounded HandlePipeEntry contract keeps its actual Down/pipe-tile/nonzero-control
checks. Twelve ROM table cases cover all control and horizontal-position bytes,
including reads beyond the named WarpZoneNumbers table. Local table cases do not
establish a legal input history or supported execution after loading the destination.

An active warp resets the level byte to zero, so this routine cannot itself produce
the project's final-victory predicate. Other world/level writers remain separate.
-/

namespace Smb.Routine.WarpDestination
open Smb.Routine

def warpCode : List UInt8 := smbPrg% 0xDEE8 99

def pipeEntry (ram : UInt16 → UInt8) : Bool :=
  ram 0x0b &&& 4 != 0 && ram 0 == 0x11 && ram 1 == 0x10

def activeWarp (ram : UInt16 → UInt8) : Bool := pipeEntry ram && ram 0x6d6 != 0

def slot (x : UInt8) : UInt8 := bif x < 0x60 then 0 else bif x < 0xa0 then 1 else 2

def tableIndex (control x : UInt8) : UInt8 := (control &&& 3) * 4 + slot x

def worldAt (prg : UInt16 → UInt8) (i : UInt8) : UInt8 := prg (0x7f2+i.toUInt16) - 1

def areaAt (prg : UInt16 → UInt8) (i : UInt8) : UInt8 :=
  prg (0x1cbc + (prg (0x1cb4 + (worldAt prg i).toUInt16)).toUInt16)

def run (s : Plain) : Plain := ((CPU.runTo (σ := Plain) 0xdf4a 50).run s).2

def Summary (sp : UInt8) (ram prg : UInt16 → UInt8) (t : Plain) : Prop :=
  let warp := activeWarp ram
  let idx := tableIndex (ram 0x6d6) (ram 0x86)
  t.bad = false ∧ t.regs.pc = 0xdf4a ∧ t.regs.s = sp ∧
  t.ram 0x770 = ram 0x770 ∧
  t.ram 0x75f = (bif warp then worldAt prg idx else ram 0x75f) ∧
  t.ram 0x750 = (bif warp then areaAt prg idx else ram 0x750) ∧
  t.ram 0x75c = (bif warp then 0 else ram 0x75c) ∧
  t.ram 0x760 = (bif warp then 0 else ram 0x760) ∧
  t.ram 0x751 = (bif warp then 0 else ram 0x751) ∧
  t.ram 0x752 = (bif warp then 0 else ram 0x752) ∧
  t.ram 0x75d = (bif warp then ram 0x75d + 1 else ram 0x75d) ∧
  t.ram 0x757 = (bif warp then ram 0x757 + 1 else ram 0x757) ∧
  t.ram 0x6de = (bif pipeEntry ram then 0x30 else ram 0x6de) ∧
  t.ram 0x0e = (bif pipeEntry ram then 3 else ram 0x0e)

set_option linter.unusedVariables false
set_option maxHeartbeats 20000000 in
theorem handlePipeEntry (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x5ee8 warpCode) (hp : p &&& 4 ≠ 0) :
    Summary sp ram prg (run ⟨⟨0xdee8,a,x,y,sp,p⟩,ram,prg,cyc,false⟩) := by
  simp only [CodeAt, warpCode, UInt16.reduceAdd] at hc
  generalize hr : run ⟨⟨0xdee8,a,x,y,sp,p⟩,ram,prg,cyc,false⟩ = f
  unfold run at hr
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [Summary, activeWarp, pipeEntry, tableIndex, slot, worldAt, areaAt, bne] at *
    fun_congr
    bv_decide

theorem rom_code : CodeAt (fun a => Smb.prg.get! (a &&& 0x7fff).toNat) 0x5ee8 warpCode :=
  codeAt_of_matches _ _ _ (by native_decide)

def actualPrg (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

/-- Rows are control low bits 0..3; columns are X<60, 60<=X<A0, X>=A0. -/
def destinations : List (UInt8 × UInt8) :=
  [(3,0x22),(2,0x24),(1,0x28),
   (0x23,1),(4,0x2a),(0x23,1),
   (7,0x30),(6,0x33),(5,0x2e),
   (0xff,0x9d),(0xff,0x9d),(0x26,0)]

/-- Twelve ROM-only table cases, including reads beyond the named tables. -/
theorem destinations_exact : ∀ row : Fin 4, ∀ col : Fin 3,
    (worldAt actualPrg (UInt8.ofNat row.val * 4 + UInt8.ofNat col.val),
     areaAt actualPrg (UInt8.ofNat row.val * 4 + UInt8.ofNat col.val)) =
      destinations.getD (3*row.val+col.val) (0,0) := by native_decide

private theorem low_bound (c : UInt8) : (c &&& 3).toNat < 4 := by
  change (c &&& 3) < (4 : UInt8)
  bv_decide
private theorem slot_bound (x : UInt8) : (slot x).toNat < 3 := by
  change slot x < (3 : UInt8)
  unfold slot
  bv_decide

/-- Exact mapping for every control byte and every horizontal position byte. -/
theorem destination_for (control x : UInt8) :
    (worldAt actualPrg (tableIndex control x), areaAt actualPrg (tableIndex control x)) =
      destinations.getD (3*(control &&& 3).toNat+(slot x).toNat) (0,0) := by
  have ht := destinations_exact ⟨(control &&& 3).toNat, low_bound control⟩
    ⟨(slot x).toNat, slot_bound x⟩
  simpa only [tableIndex, UInt8.ofNat_toNat] using ht

def worldImage : List UInt8 := [1,2,3,4,5,6,7,0x23,0x26,0xff]

private theorem tableImage : ∀ row : Fin 4, ∀ col : Fin 3,
    (destinations.getD (3*row.val+col.val) (0,0)).1 ∈ worldImage := by decide

theorem world_in_image (control x : UInt8) :
    worldAt actualPrg (tableIndex control x) ∈ worldImage := by
  have ht := tableImage ⟨(control &&& 3).toNat, low_bound control⟩
    ⟨(slot x).toNat, slot_bound x⟩
  have he := congrArg Prod.fst (destination_for control x)
  dsimp only at he
  rw [he]
  exact ht

/-- Enabled warp selection resets level to zero; it cannot itself enter the final predicate. -/
theorem warp_cannot_finish (sp : UInt8) (ram prg : UInt16 → UInt8) (t : Plain)
    (h : Summary sp ram prg t) (hw : activeWarp ram = true) :
    (t.ram 0x770 == 2 && t.ram 0x75f == 7 && t.ram 0x75c == 3) = false := by
  have hl := h.2.2.2.2.2.2.1
  simp only [hw, Bool.cond_true] at hl
  simp [hl]

/-- The bounded CPU contract instantiated with the actual cartridge PRG. -/
theorem handlePipeEntry_rom (a x y sp p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hp : p &&& 4 ≠ 0) :
    Summary sp ram actualPrg (run ⟨⟨0xdee8,a,x,y,sp,p⟩,ram,actualPrg,cyc,false⟩) :=
  handlePipeEntry a x y sp p ram actualPrg cyc rom_code hp

theorem active_world_image (sp : UInt8) (ram : UInt16 → UInt8) (t : Plain)
    (h : Summary sp ram actualPrg t) (hw : activeWarp ram = true) :
    t.ram 0x75f ∈ worldImage := by
  have he := h.2.2.2.2.1
  simp only [hw, Bool.cond_true] at he
  rw [he]
  exact world_in_image (ram 0x6d6) (ram 0x86)

/-- A changed world byte at this writer requires the full pipe and nonzero-control guard. -/
theorem changed_world_requires_guard (sp : UInt8) (ram prg : UInt16 → UInt8) (t : Plain)
    (h : Summary sp ram prg t) (hc : t.ram 0x75f ≠ ram 0x75f) : activeWarp ram = true := by
  have he := h.2.2.2.2.1
  by_cases hw : activeWarp ram = true
  · exact hw
  · have hw' : activeWarp ram = false := Bool.eq_false_iff.mpr hw
    simp only [hw', Bool.cond_false] at he
    exact False.elim (hc he)

end Smb.Routine.WarpDestination
