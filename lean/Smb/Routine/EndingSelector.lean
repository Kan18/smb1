import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# Ending selectors do not themselves require level three

The actual world-8 message branch queues selector $0F with an arbitrary level byte.
The later end-world gate compares world >=7. These local contracts make an existing
finish-specification gap precise; they do not establish a reachable exceptional ending,
rendered pixels or a counterexample to the current upper-bound certificate.
Any bridge from these events to the project's three-byte goal must justify its level
and timing conditions on reachable histories. The Game definition is unchanged.
-/

namespace Smb.Routine.EndingSelector
open Smb.Routine

/- Local actual-code contracts only. No initial-state reachability or legal win is claimed.
The message routine stops before RTS, and the world gate stops before reading buttons. -/
def messageCode : List UInt8 := smbPrg% 0x83F6 107
def endGateCode : List UInt8 := smbPrg% 0x8461 12

def MessagePost (x sp : UInt8) (ram prg : UInt16 → UInt8) (t : Plain) : Prop :=
  t.bad = false ∧ t.regs.pc = 0x8460 ∧ t.regs.s = sp ∧ t.regs.x = x ∧
  t.prg = prg ∧ t.ram 0x773 = 0x0f ∧ t.ram 0xfc = 4 ∧
  t.ram 0x749 = 4 ∧ t.ram 0x719 = 3 ∧
  t.ram 0x75c = ram 0x75c ∧ t.ram 0x75f = 7 ∧
  t.ram 0x770 = ram 0x770 ∧ t.ram 0x772 = ram 0x772 ∧
  t.ram 0x7a1 = ram 0x7a1

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000 in
theorem world8_message (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x03f6 messageCode) (hp : p &&& 4 ≠ 0)
    (hprimary : ram 0x719 = 3) (hsecondary : ram 0x749 = 0)
    (hworld : ram 0x75f = 7) :
    MessagePost x sp ram prg ((CPU.runTo (σ := Plain) 0x8460 45).run
      ⟨⟨0x83f6,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, messageCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x8460 45).run
    ⟨⟨0x83f6,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI,hprimary,hsecondary,hworld]
  all_goals
    intros
    clear hc hI
    simp only [MessagePost] at *
    fun_congr
    bv_decide

set_option maxHeartbeats 4000000 in
theorem end_world_gate (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x0461 endGateCode) (hp : p &&& 4 ≠ 0)
    (htimer : ram 0x7a1 = 0) (hworld : 7 ≤ ram 0x75f) :
    let t := ((CPU.runTo (σ := Plain) 0x8487 7).run
      ⟨⟨0x8461,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2
    t.bad = false ∧ t.regs.pc = 0x8487 ∧ t.regs.s = sp ∧
      t.ram = ram ∧ t.prg = prg := by
  dsimp only
  simp only [CodeAt, endGateCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x8487 7).run
    ⟨⟨0x8461,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI,htimer,hworld]
  all_goals
    intros
    clear hc hI
    simp_all <;> fun_congr <;> bv_decide

def actualPrg (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

theorem rom_message : CodeAt actualPrg 0x03f6 messageCode :=
  codeAt_of_matches _ _ _ (by native_decide)
theorem rom_endGate : CodeAt actualPrg 0x0461 endGateCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem world8_message_rom (a x y sp p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hp : p &&& 4 ≠ 0) (hprimary : ram 0x719 = 3) (hsecondary : ram 0x749 = 0)
    (hworld : ram 0x75f = 7) :
    MessagePost x sp ram actualPrg ((CPU.runTo (σ := Plain) 0x8460 45).run
      ⟨⟨0x83f6,a,x,y,sp,p⟩,ram,actualPrg,cyc,false⟩).2 :=
  world8_message a x y sp p ram actualPrg cyc rom_message hp hprimary hsecondary hworld

end Smb.Routine.EndingSelector
