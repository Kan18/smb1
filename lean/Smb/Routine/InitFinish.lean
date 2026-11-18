import Smb.Data.ProofRom
import Smb.Routine.FinishWrites

/-!
# Initializer entry, body and loop-back cuts

Entry establishes A=0. The body and footer retain A, I and PRG so later cuts can
reuse their premises. Initial bad is arbitrary: the body may set it, and the footer
preserves the actual incoming value rather than resetting it. These are local
contracts, not a full memory-clear, return, termination or all-prefix theorem.
-/

namespace Smb.Routine.FinishWrites.InitLoop
open Smb.Routine


def loopCode : List UInt8 := smbPrg% 0x90D2 21

set_option linter.unusedVariables false
/- A=0 is explicit here; entry_setup below establishes it from the actual LDA.
The initial bad flag is arbitrary, and the final bad flag is deliberately unconstrained.
The footer preserves A and I on every ordinary loop-back edge without clearing bad. -/
set_option maxHeartbeats 20000000 in
theorem body_assuming_zero (x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hc : CodeAt prg 0x10d2 loopCode) (hp : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x90d4,0,x,y,sp,p⟩,ram,prg,cyc,bad⟩
    let t := ((CPU.runTo (σ := Plain) 0x90de 6).run s).2
    t.prg = prg ∧ t.regs.pc = 0x90de ∧ t.regs.a = 0 ∧ t.regs.s = sp ∧ t.regs.p &&& 4 ≠ 0 ∧
      (finish t = true → finish s = true) := by
  dsimp only
  simp only [CodeAt, loopCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x90de 6).run
    ⟨⟨0x90d4,0,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [finish] at *
    fun_congr
    bv_decide

def FooterSummary (a sp : UInt8) (bad : Bool) (ram prg : UInt16 → UInt8) (t : Plain) : Prop :=
  t.prg = prg ∧ t.bad = bad ∧ (t.regs.pc = 0x90d4 ∨ t.regs.pc = 0x90e6) ∧
  t.regs.a = a ∧ t.regs.s = sp ∧ t.regs.p &&& 4 ≠ 0 ∧
  finish t = (ram 0x770 == 2 && ram 0x75f == 7 && ram 0x75c == 3)

/- Bounded continuation cut: stop at the next loop-body entry or before RTS.
This avoids requiring callers to predict which branch is taken. -/
set_option maxHeartbeats 20000000 in
theorem footer_reach (stop : UInt16)
    (hstop : ∀ pc : UInt16, (0x90d2 ≤ pc && pc ≤ 0x90e6) = true → pc ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hc : CodeAt prg 0x10d2 loopCode) (hp : p &&& 4 ≠ 0) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m+8)).run
      ⟨⟨0x90de,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2 =
      ((CPU.runTo stop (j+m)).run t).2 ∧ FooterSummary a sp bad ram prg t := by
  simp only [CodeAt, loopCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) stop (m+8)).run
    ⟨⟨0x90de,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2 = f
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI] until [37076,37094]
  all_goals
    intros
    clear hc hI
    subst hr
    reach_finish [FooterSummary,finish]

/- The actual three-instruction setup ends exactly at the loop-body entry.
Only fixed low RAM addresses are written, so even an existing bad flag is preserved. -/
def entryCode : List UInt8 := smbPrg% 0x90CE 6

set_option maxHeartbeats 20000000 in
theorem entry_setup (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hc : CodeAt prg 0x10ce entryCode) (hp : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x90ce,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩
    let t := ((CPU.runTo (σ := Plain) 0x90d4 4).run s).2
    t.prg = prg ∧ t.bad = bad ∧ t.regs.pc = 0x90d4 ∧ t.regs.a = 0 ∧
    t.regs.s = sp ∧ t.regs.p &&& 4 ≠ 0 ∧
    t.ram 6 = 0 ∧ t.ram 7 = x ∧ finish t = finish s := by
  dsimp only
  simp only [CodeAt, entryCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x90d4 4).run
    ⟨⟨0x90ce,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [finish] at *
    fun_congr
    bv_decide

theorem rom_entry : CodeAt (fun a => Smb.prg.get! (a &&& 0x7fff).toNat) 0x10ce entryCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_loop : CodeAt (fun a => Smb.prg.get! (a &&& 0x7fff).toNat) 0x10d2 loopCode :=
  codeAt_of_matches _ _ _ (by native_decide)

end Smb.Routine.FinishWrites.InitLoop
