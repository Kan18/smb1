import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# Warp-zone control writers

Bounded actual-ROM contracts for the warp-zone object's guard/increment/erase path
and the selector prefix before WriteGameText. Object execution stops before either
RTS. Its slot stores include stack-page cells, so preserving S does not prove an
arbitrary caller's return address intact. All call-site and stream-history obligations
remain separate; neither contract establishes a legal path to a new destination.
-/

namespace Smb.Routine.WarpControl
open Smb.Routine

/-- Includes the earlier guard-failure RTS and the WarpZoneObject body. -/
def objectCode : List UInt8 := smbPrg% 0xB7A3 21
/-- EraseEnemyObject, including its unexecuted final RTS. -/
def eraseCode : List UInt8 := smbPrg% 0xC998 24
/-- Selector only: stop at $9705 before WriteGameText or later side effects. -/
def setterCode : List UInt8 := smbPrg% 0x96F2 19

def enabled (ram : UInt16 → UInt8) : Bool :=
  ram 0x723 != 0 && ram 0xce &&& ram 0xb5 == 0

def idx (base : UInt16) (x : UInt8) : UInt16 := base+x.toUInt16

def objectRun (s : Plain) : Plain :=
  ((CPU.runTo (σ := Plain) (bif enabled s.ram then 0xc9af else 0xb7a3) 25).run s).2

def ObjectSummary (x sp : UInt8) (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.bad = false ∧ t.regs.pc = (bif enabled ram then 0xc9af else 0xb7a3) ∧
  t.regs.s = sp ∧ t.regs.x = x ∧
  t.ram 0x6d6 = (bif enabled ram then ram 0x6d6+1 else ram 0x6d6) ∧
  t.ram 0x723 = (bif enabled ram then 0 else ram 0x723) ∧
  t.ram 0x770 = ram 0x770 ∧ t.ram 0x74e = ram 0x74e ∧
  t.ram (idx 0x0f x) = (bif enabled ram then 0 else ram (idx 0x0f x)) ∧
  t.ram (idx 0x16 x) = (bif enabled ram then 0 else ram (idx 0x16 x)) ∧
  t.ram (idx 0x1e x) = (bif enabled ram then 0 else ram (idx 0x1e x)) ∧
  t.ram (idx 0x110 x) = (bif enabled ram then 0 else ram (idx 0x110 x)) ∧
  t.ram (idx 0x796 x) = (bif enabled ram then 0 else ram (idx 0x796 x)) ∧
  t.ram (idx 0x125 x) = (bif enabled ram then 0 else ram (idx 0x125 x)) ∧
  t.ram (idx 0x3c5 x) = (bif enabled ram then 0 else ram (idx 0x3c5 x)) ∧
  t.ram (idx 0x78a x) = (bif enabled ram then 0 else ram (idx 0x78a x))

set_option linter.unusedVariables false
set_option maxHeartbeats 20000000 in
theorem warpObject (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x37a3 objectCode) (he : CodeAt prg 0x4998 eraseCode)
    (hp : p &&& 4 ≠ 0) (hx : x < 6) :
    ObjectSummary x sp ram (objectRun ⟨⟨0xb7a4,a,x,y,sp,p⟩,ram,prg,cyc,false⟩) := by
  simp only [CodeAt, objectCode, UInt16.reduceAdd] at hc
  simp only [CodeAt, eraseCode, UInt16.reduceAdd] at he
  cases hg : enabled ram
  all_goals
    generalize hr : objectRun ⟨⟨0xb7a4,a,x,y,sp,p⟩,ram,prg,cyc,false⟩ = f
    unfold objectRun at hr
    simp only [hg, Bool.cond_false, Bool.cond_true] at hr
    have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
    have hguard := hg
    simp only [enabled, bne] at hguard
    sym_run hr [hc,he,hI,hguard,hx]
  all_goals
    intros
    clear hc he hI
    simp only [ObjectSummary, enabled, idx, bne] at *
    fun_congr
    bv_decide

def selected (ram : UInt16 → UInt8) : UInt8 :=
  bif ram 0x75f == 0 then 4 else bif ram 0x74e == 1 then 6 else 5

def setterRun (s : Plain) : Plain := ((CPU.runTo (σ := Plain) 0x9705 12).run s).2

def SetterSummary (sp : UInt8) (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.bad = false ∧ t.regs.pc = 0x9705 ∧ t.regs.s = sp ∧
  t.regs.a = selected ram ∧ t.regs.x = selected ram ∧
  t.ram 0x6d6 = selected ram ∧ t.ram 0x770 = ram 0x770 ∧
  t.ram 0x723 = ram 0x723 ∧ t.ram 0x74e = ram 0x74e ∧ t.ram 0x75f = ram 0x75f

set_option maxHeartbeats 20000000 in
theorem warpSetter (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x16f2 setterCode) (hp : p &&& 4 ≠ 0) :
    SetterSummary sp ram (setterRun ⟨⟨0x96f2,a,x,y,sp,p⟩,ram,prg,cyc,false⟩) := by
  simp only [CodeAt, setterCode, UInt16.reduceAdd] at hc
  generalize hr : setterRun ⟨⟨0x96f2,a,x,y,sp,p⟩,ram,prg,cyc,false⟩ = f
  unfold setterRun at hr
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [SetterSummary, selected] at *
    fun_congr
    bv_decide

def actualPrg (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

theorem rom_object : CodeAt actualPrg 0x37a3 objectCode :=
  codeAt_of_matches _ _ _ (by native_decide)
theorem rom_erase : CodeAt actualPrg 0x4998 eraseCode :=
  codeAt_of_matches _ _ _ (by native_decide)
theorem rom_setter : CodeAt actualPrg 0x16f2 setterCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem warpObject_rom (a x y sp p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hp : p &&& 4 ≠ 0) (hx : x < 6) :
    ObjectSummary x sp ram (objectRun ⟨⟨0xb7a4,a,x,y,sp,p⟩,ram,actualPrg,cyc,false⟩) :=
  warpObject a x y sp p ram actualPrg cyc rom_object rom_erase hp hx

theorem warpSetter_rom (a x y sp p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hp : p &&& 4 ≠ 0) :
    SetterSummary sp ram (setterRun ⟨⟨0x96f2,a,x,y,sp,p⟩,ram,actualPrg,cyc,false⟩) :=
  warpSetter a x y sp p ram actualPrg cyc rom_setter hp

/-- A local fact about this store, without a normal-world or normal-area assumption. -/
theorem selected_six_iff (ram : UInt16 → UInt8) :
    selected ram = 6 ↔ ram 0x75f ≠ 0 ∧ ram 0x74e = 1 := by
  simp only [selected]
  bv_decide

theorem selected_image (ram : UInt16 → UInt8) :
    selected ram = 4 ∨ selected ram = 5 ∨ selected ram = 6 := by
  simp only [selected]
  bv_decide

/-- Every enabled increment changes the byte, including wrapping FF to 00. -/
theorem control_changes_iff (x sp : UInt8) (ram : UInt16 → UInt8) (t : Plain)
    (h : ObjectSummary x sp ram t) :
    (t.ram 0x6d6 ≠ ram 0x6d6) ↔ enabled ram = true := by
  have hc := h.2.2.2.2.1
  rw [hc]
  generalize ram 0x6d6 = c
  cases he : enabled ram <;> simp only [Bool.cond_false, Bool.cond_true] <;> bv_decide

/-! These event histories intentionally allow more orderings than the ordinary
streams, but are not a verified abstraction of all legal inputs. Fresh initialization,
intended pointers and at most one object activation remain separate obligations. -/
namespace StreamHistory

/-- Conditional per-underground-area history: fresh zero, arbitrary text stores 4/5,
    and at most one consumption of the sole ID $34 record. This is an abstraction,
    not a proved refinement of the ROM parser or an assertion about legal reachability. -/
inductive Underground : UInt8 → Bool → Prop where
  | initial : Underground 0 false
  | text4 {c used} : Underground c used → Underground 4 used
  | text5 {c used} : Underground c used → Underground 5 used
  | consume {c} : Underground c false → Underground (c+1) true

def Allowed (c : UInt8) (used : Bool) : Prop :=
  if used then c=1 ∨ c=4 ∨ c=5 ∨ c=6 else c=0 ∨ c=4 ∨ c=5

theorem underground_allowed {c used} (h : Underground c used) : Allowed c used := by
  induction h with
  | initial => unfold Allowed; decide
  | @text4 c used h ih => cases used <;> unfold Allowed <;> decide
  | @text5 c used h ih => cases used <;> unfold Allowed <;> decide
  | @consume c h ih =>
    change c=0 ∨ c=4 ∨ c=5 at ih
    rcases ih with rfl | rfl | rfl <;> unfold Allowed <;> decide

/-- Even permitting the sole increment after a text store, row 3 cannot be selected. -/
theorem underground_not_row3 {c used} (h : Underground c used) : c &&& 3 ≠ 3 := by
  have hc := underground_allowed h
  cases used with
  | false =>
    change c=0 ∨ c=4 ∨ c=5 at hc
    rcases hc with rfl | rfl | rfl <;> decide
  | true =>
    change c=1 ∨ c=4 ∨ c=5 ∨ c=6 at hc
    rcases hc with rfl | rfl | rfl | rfl <;> decide

/-- Conditional ground-area history: no ID $34 source, only fresh zero and text stores. -/
inductive Ground : UInt8 → Prop where
  | initial : Ground 0
  | text4 {c} : Ground c → Ground 4
  | text6 {c} : Ground c → Ground 6

theorem ground_not_row3 {c} (h : Ground c) : c &&& 3 ≠ 3 := by
  cases h <;> decide

/-- Store 5 then consume is allowed by the conservative underground abstraction. -/
theorem store5_then_increment : Underground 6 true :=
  Underground.consume (Underground.text5 Underground.initial)


/-- Connect an actual object summary to the event invariant. The one-consumption
    budget is an explicit history premise, not a fact supplied by the local routine. -/
theorem after_object {x sp : UInt8} {ram : UInt16 → UInt8} {t : Plain} {used : Bool}
    (history : Underground (ram 0x6d6) used)
    (budget : enabled ram = true → used = false)
    (call : ObjectSummary x sp ram t) :
    Underground (t.ram 0x6d6) (used || enabled ram) := by
  have hc := call.2.2.2.2.1
  cases he : enabled ram with
  | false =>
    simp only [he, Bool.cond_false] at hc
    simpa only [he, Bool.or_false, hc] using history
  | true =>
    have hu := budget he
    subst used
    simp only [he, Bool.cond_true] at hc
    simpa only [he, Bool.or_true, hc] using Underground.consume history

/-- A local text-store summary in underground type 2 preserves the event model. -/
theorem after_underground_setter {sp : UInt8} {ram : UInt16 → UInt8} {t : Plain} {used : Bool}
    (history : Underground (ram 0x6d6) used) (htype : ram 0x74e = 2)
    (call : SetterSummary sp ram t) : Underground (t.ram 0x6d6) used := by
  have hc := call.2.2.2.2.2.1
  by_cases hw : ram 0x75f = 0
  · have hs : selected ram = 4 := by
      unfold selected
      rw [hw]
      rfl
    rw [hc, hs]
    exact Underground.text4 history
  · have hs : selected ram = 5 := by
      unfold selected
      simp only [beq_false_of_ne hw, Bool.cond_false, htype]
      rfl
    rw [hc, hs]
    exact Underground.text5 history

/-- The corresponding text-store bridge for ground type 1. Absence of an object
    increment remains a premise of the ground history, not an area-type theorem. -/
theorem after_ground_setter {sp : UInt8} {ram : UInt16 → UInt8} {t : Plain}
    (history : Ground (ram 0x6d6)) (htype : ram 0x74e = 1)
    (call : SetterSummary sp ram t) : Ground (t.ram 0x6d6) := by
  have hc := call.2.2.2.2.2.1
  by_cases hw : ram 0x75f = 0
  · have hs : selected ram = 4 := by
      unfold selected
      rw [hw]
      rfl
    rw [hc, hs]
    exact Ground.text4 history
  · have hs : selected ram = 6 := by
      unfold selected
      simp only [beq_false_of_ne hw, Bool.cond_false, htype]
      rfl
    rw [hc, hs]
    exact Ground.text6 history

end StreamHistory

end Smb.Routine.WarpControl
