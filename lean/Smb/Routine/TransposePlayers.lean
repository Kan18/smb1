import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# Switching players preserves the two saved progress records

A bounded execution of TransposePlayers swaps the seven-byte player records when
its guard allows, preserves OperMode, and restores every wrapping stack pointer.
The world/level pair is unchanged or exchanged, so its maximum is preserved even
without assuming ordinary byte ranges or one-player mode.

The NES transfer uses the existing quiet-run refinement assumptions. It proves
CPU/RAM effects and makes no claim that the PPU's unsupported flag stays false.
-/

namespace Smb.Routine.TransposePlayers
open Smb.Routine

/-- Actual ROM bytes $9282 through $92A9; the bounded run stops before RTS. -/
def transposeCode : List UInt8 := smbPrg% 0x9282 40

def enabled (ram : UInt16 → UInt8) : Bool :=
  ram 0x77a != 0 && ram 0x761 &&& 0x80 == 0

def run (s : Plain) : Plain := ((CPU.runTo (σ := Plain) 0x92a9 70).run s).2

def Summary (sp : UInt8) (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.bad = false ∧ t.regs.pc = 0x92a9 ∧ t.regs.s = sp ∧
  t.ram 0x770 = ram 0x770 ∧
  t.ram 0x753 = (bif enabled ram then ram 0x753 ^^^ 1 else ram 0x753) ∧
  (∀ i : UInt16, i < 7 →
    t.ram (0x75a+i) = (bif enabled ram then ram (0x761+i) else ram (0x75a+i)) ∧
    t.ram (0x761+i) = (bif enabled ram then ram (0x75a+i) else ram (0x761+i)))

set_option linter.unusedVariables false
set_option maxHeartbeats 20000000 in
theorem transpose (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x1282 transposeCode) (hp : p &&& 4 ≠ 0) :
    Summary sp ram (run ⟨⟨0x9282,a,x,y,sp,p⟩,ram,prg,cyc,false⟩) := by
  simp only [CodeAt, transposeCode, UInt16.reduceAdd] at hcode
  generalize hrun : run ⟨⟨0x9282,a,x,y,sp,p⟩,ram,prg,cyc,false⟩ = f
  unfold run at hrun
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hrun [hcode, hI]
  all_goals
    intros
    clear hcode hI
    simp only [Summary, enabled, bne] at *
    simp only [← and_assoc]
    refine ⟨?_, fun i hi => ?_⟩ <;> fun_congr <;> bv_decide

/-- ROM identity only; no movie or prefix execution. -/
theorem rom_transpose :
    CodeAt (fun a => Smb.prg.get! (a &&& 0x7fff).toNat) 0x1282 transposeCode :=
  codeAt_of_matches _ _ _ (by native_decide)

/-- Zero-indexed world and level bytes for the two player slots. -/
def onProgress (ram : UInt16 → UInt8) : UInt8 × UInt8 := (ram 0x75f, ram 0x75c)
def offProgress (ram : UInt16 → UInt8) : UInt8 × UInt8 := (ram 0x766, ram 0x763)

/-- A total lexical code, valid even for bytes outside ordinary game ranges. -/
def progressValue (p : UInt8 × UInt8) : Nat := p.1.toNat * 256 + p.2.toNat

/-- The pair is unchanged or swapped, which preserves its unordered contents. -/
theorem progressPair (sp : UInt8) (ram : UInt16 → UInt8) (t : Plain)
    (h : Summary sp ram t) :
    (onProgress t.ram = onProgress ram ∧ offProgress t.ram = offProgress ram) ∨
    (onProgress t.ram = offProgress ram ∧ offProgress t.ram = onProgress ram) := by
  rcases h with ⟨hb, hpc, hs, hm, hc, hbytes⟩
  have h2 := hbytes 2 (by decide)
  have h5 := hbytes 5 (by decide)
  simp only [UInt16.reduceAdd] at h2 h5
  by_cases he : enabled ram = true
  · right
    simp only [he, Bool.cond_true] at h2 h5
    exact ⟨Prod.ext h5.1 h2.1, Prod.ext h5.2 h2.2⟩
  · left
    have he' : enabled ram = false := Bool.eq_false_iff.mpr he
    simp only [he', Bool.cond_false] at h2 h5
    exact ⟨Prod.ext h5.1 h2.1, Prod.ext h5.2 h2.2⟩

theorem maxProgress (sp : UInt8) (ram : UInt16 → UInt8) (t : Plain)
    (h : Summary sp ram t) :
    max (progressValue (onProgress t.ram)) (progressValue (offProgress t.ram)) =
      max (progressValue (onProgress ram)) (progressValue (offProgress ram)) := by
  rcases progressPair sp ram t h with ⟨ho, hf⟩ | ⟨ho, hf⟩
  · rw [ho, hf]
  · rw [ho, hf, Nat.max_comm]

private theorem infoBounds (i : UInt16) (hi : i < 7) :
    0x75a+i < 0x800 ∧ 0x761+i < 0x800 := by bv_decide

/-- Full NES CPU/RAM contract under the existing quiet-run refinement assumptions.
    No conclusion is made about the PPU's unsupported flag during the run. -/
theorem transpose_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg)
    (hpc : s.pc = 0x9282) (hp : s.p &&& 4 ≠ 0) :
    let t := ((CPU.runTo (σ := NES) 0x92a9 70).run s).2
    t.pc = 0x92a9 ∧ t.s = s.s ∧ ramAt t 0x770 = ramAt s 0x770 ∧
    ramAt t 0x753 = (bif enabled (ramAt s) then ramAt s 0x753 ^^^ 1 else ramAt s 0x753) ∧
    (∀ i : UInt16, i < 7 →
      ramAt t (0x75a+i) = (bif enabled (ramAt s) then ramAt s (0x761+i) else ramAt s (0x75a+i)) ∧
      ramAt t (0x761+i) = (bif enabled (ramAt s) then ramAt s (0x75a+i) else ramAt s (0x761+i))) := by
  intro t
  have ht : s.toPlain = ⟨⟨0x9282,s.a,s.x,s.y,s.s,s.p⟩,ramAt s,
      fun a => s.prg.get! (a &&& 0x7fff).toNat,s.cyc,false⟩ := by
    simp only [NES.toPlain, hpc]; rfl
  have hc : CodeAt (fun a => s.prg.get! (a &&& 0x7fff).toNat) 0x1282 transposeCode := by
    rw [hprg]; exact rom_transpose
  have hsum := transpose s.a s.x s.y s.s s.p (ramAt s) _ s.cyc hc hp
  rw [← ht] at hsum
  rcases hsum with ⟨hb, hpc', hs, hm, hcur, hbytes⟩
  unfold run at hb hpc' hs hm hcur hbytes
  have hr := refine_runTo s hq 0x92a9 70 hb
  have hmem (i : UInt16) (hi : i < 0x800) :
      ramAt t i = ((CPU.runTo (σ := Plain) 0x92a9 70).run s.toPlain).2.ram i := by
    rw [ramAt_of_rel hr, and7ff_of_lt i hi]
  refine ⟨(congrArg Regs.pc hr.regs).trans hpc', (congrArg Regs.s hr.regs).trans hs,
    (hmem 0x770 (by decide)).trans hm, (hmem 0x753 (by decide)).trans hcur, ?_⟩
  intro i hi
  have hbounds := infoBounds i hi
  rw [hmem (0x75a+i) hbounds.1, hmem (0x761+i) hbounds.2]
  exact hbytes i hi

/-- The full NES run preserves the unordered pair of player progress values and its maximum. -/
theorem transpose_nes_progress (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg)
    (hpc : s.pc = 0x9282) (hp : s.p &&& 4 ≠ 0) :
    let t := ((CPU.runTo (σ := NES) 0x92a9 70).run s).2
    ((onProgress (ramAt t) = onProgress (ramAt s) ∧ offProgress (ramAt t) = offProgress (ramAt s)) ∨
     (onProgress (ramAt t) = offProgress (ramAt s) ∧ offProgress (ramAt t) = onProgress (ramAt s))) ∧
    max (progressValue (onProgress (ramAt t))) (progressValue (offProgress (ramAt t))) =
      max (progressValue (onProgress (ramAt s))) (progressValue (offProgress (ramAt s))) := by
  intro t
  have ht := transpose_nes s hq hprg hpc hp
  have hsum : Summary s.s (ramAt s) t.toPlain :=
    ⟨rfl, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩
  exact ⟨progressPair s.s (ramAt s) t.toPlain hsum, maxProgress s.s (ramAt s) t.toPlain hsum⟩

end Smb.Routine.TransposePlayers
