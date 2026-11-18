import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# Local indirect writes and the finish predicate

These bounded instruction fragments include the constant load or pointer setup
before the indirect store. They do not assume an arbitrary STA has the ordinary
accumulator value, and do not establish global control-flow provenance.

The constant-store fragments cannot create the finish predicate at any destination
in Plain; they make no final bad=false claim. The delayed updater sets pointer high
byte 5, so arbitrary low/row bytes remain below $0700 and preserve the finish cells.
Its fragment is Plain-supported. No theorem covers the following JSR/RTS or a
whole handler; initializer loop revisits need separate accumulator provenance.
-/

namespace Smb.Routine.FinishWrites
open Smb.Routine

/-- The project's three-byte finish predicate on Plain RAM. -/
def finish (s : Plain) : Bool := s.ram 0x770 == 2 && s.ram 0x75f == 7 && s.ram 0x75c == 3

set_option linter.unusedVariables false

def vineCode : List UInt8 := smbPrg% 0xB9B3 4
/- Includes LDA #$26, not merely an isolated STA with an assumed accumulator. -/
set_option maxHeartbeats 20000000 in
theorem vine_cut (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x39b3 vineCode) (hp : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0xb9b3,a,x,y,sp,p⟩,ram,prg,cyc,false⟩
    let t := ((CPU.runTo (σ := Plain) 0xb9b7 3).run s).2
    t.regs.pc = 0xb9b7 ∧ t.regs.s = sp ∧ t.regs.a = 0x26 ∧
      (finish t = true → finish s = true) := by
  dsimp only
  simp only [CodeAt, vineCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0xb9b7 3).run
    ⟨⟨0xb9b3,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [finish] at *
    fun_congr
    bv_decide

def blockCode : List UInt8 := smbPrg% 0xBD49 4
/- Includes LDA #$23, not merely an isolated STA with an assumed accumulator. -/
set_option maxHeartbeats 20000000 in
theorem block_cut (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x3d49 blockCode) (hp : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0xbd49,a,x,y,sp,p⟩,ram,prg,cyc,false⟩
    let t := ((CPU.runTo (σ := Plain) 0xbd4d 3).run s).2
    t.regs.pc = 0xbd4d ∧ t.regs.s = sp ∧ t.regs.a = 0x23 ∧
      (finish t = true → finish s = true) := by
  dsimp only
  simp only [CodeAt, blockCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0xbd4d 3).run
    ⟨⟨0xbd49,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [finish] at *
    fun_congr
    bv_decide

def zeroCode : List UInt8 := smbPrg% 0xBE33 4
/- Includes LDA #$00, not merely an isolated STA with an assumed accumulator. -/
set_option maxHeartbeats 20000000 in
theorem coin_cut (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x3e33 zeroCode) (hp : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0xbe33,a,x,y,sp,p⟩,ram,prg,cyc,false⟩
    let t := ((CPU.runTo (σ := Plain) 0xbe37 3).run s).2
    t.regs.pc = 0xbe37 ∧ t.regs.s = sp ∧ t.regs.a = 0x0 ∧
      (finish t = true → finish s = true) := by
  dsimp only
  simp only [CodeAt, zeroCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0xbe37 3).run
    ⟨⟨0xbe33,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [finish] at *
    fun_congr
    bv_decide

/- Includes LDA #$00, not merely an isolated STA with an assumed accumulator. -/
set_option maxHeartbeats 20000000 in
theorem axeErase_cut (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x5e1e zeroCode) (hp : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0xde1e,a,x,y,sp,p⟩,ram,prg,cyc,false⟩
    let t := ((CPU.runTo (σ := Plain) 0xde22 3).run s).2
    t.regs.pc = 0xde22 ∧ t.regs.s = sp ∧ t.regs.a = 0x0 ∧
      (finish t = true → finish s = true) := by
  dsimp only
  simp only [CodeAt, zeroCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0xde22 3).run
    ⟨⟨0xde1e,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [finish] at *
    fun_congr
    bv_decide

/- Includes LDA #$00, not merely an isolated STA with an assumed accumulator. -/
set_option maxHeartbeats 20000000 in
theorem enemyErase_cut (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x6005 zeroCode) (hp : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0xe005,a,x,y,sp,p⟩,ram,prg,cyc,false⟩
    let t := ((CPU.runTo (σ := Plain) 0xe009 3).run s).2
    t.regs.pc = 0xe009 ∧ t.regs.s = sp ∧ t.regs.a = 0x0 ∧
      (finish t = true → finish s = true) := by
  dsimp only
  simp only [CodeAt, zeroCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0xe009 3).run
    ⟨⟨0xe005,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [finish] at *
    fun_congr
    bv_decide

def initCode : List UInt8 := smbPrg% 0x90CE 16
/- Establish A=0 and pointer setup, then perform or skip this iteration's write.
No assumption is made that the arbitrary page X is RAM, hence no bad=false conclusion. -/
set_option maxHeartbeats 20000000 in
theorem init_cut (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x10ce initCode) (hp : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x90ce,a,x,y,sp,p⟩,ram,prg,cyc,false⟩
    let t := ((CPU.runTo (σ := Plain) 0x90de 9).run s).2
    t.regs.pc = 0x90de ∧ t.regs.s = sp ∧ t.regs.a = 0 ∧
      (finish t = true → finish s = true) := by
  dsimp only
  simp only [CodeAt, initCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x90de 9).run
    ⟨⟨0x90ce,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [finish] at *
    fun_congr
    bv_decide

def updateCode : List UInt8 := smbPrg% 0xBEE2 20
def destination (ram : UInt16 → UInt8) (x : UInt8) : UInt16 :=
  0x500 + (ram (0x3e6+x.toUInt16)).toUInt16 + (ram (0x3e4+x.toUInt16)).toUInt16

theorem destination_bounds (lo y : UInt8) :
    0x500 ≤ (0x500 + lo.toUInt16 + y.toUInt16 : UInt16) ∧
    (0x500 + lo.toUInt16 + y.toUInt16 : UInt16) ≤ 0x6fe := by bv_decide

/- Actual low/high pointer setup and Y load; arbitrary X and source bytes. -/
set_option maxHeartbeats 20000000 in
theorem update_cut (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x3ee2 updateCode) (hp : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0xbee2,a,x,y,sp,p⟩,ram,prg,cyc,false⟩
    let t := ((CPU.runTo (σ := Plain) 0xbef6 10).run s).2
    t.bad = false ∧ t.regs.pc = 0xbef6 ∧ t.regs.s = sp ∧
    t.ram 7 = 5 ∧
    t.ram (destination ram x) = ram (0x3e8+x.toUInt16) ∧
    t.ram 0x770 = ram 0x770 ∧ t.ram 0x75f = ram 0x75f ∧ t.ram 0x75c = ram 0x75c ∧
    finish t = finish s := by
  dsimp only
  simp only [CodeAt, updateCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0xbef6 10).run
    ⟨⟨0xbee2,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [finish, destination] at *
    fun_congr
    bv_decide

def actualPrg (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

theorem rom_vine : CodeAt actualPrg 0x39b3 vineCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_block : CodeAt actualPrg 0x3d49 blockCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_coin : CodeAt actualPrg 0x3e33 zeroCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_axeErase : CodeAt actualPrg 0x5e1e zeroCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_enemyErase : CodeAt actualPrg 0x6005 zeroCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_init : CodeAt actualPrg 0x10ce initCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_update : CodeAt actualPrg 0x3ee2 updateCode :=
  codeAt_of_matches _ _ _ (by native_decide)

end Smb.Routine.FinishWrites
