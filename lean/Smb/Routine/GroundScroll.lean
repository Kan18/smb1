import Smb.Data.ProofRom
import Smb.Routine.MemoryContracts
import Std.WP
import Std.Tactic.Do

/-!
# The real ground-movement call, return, and scroll store

This bounded Plain-machine result covers $B366..$B36B: JSR MovePlayerHorizontally,
its RTS, and STA Player_X_Scroll. The callee is reused through its checked contract;
its RAM function stays opaque and return-byte facts come from MemoryContracts.

Both jumpspring paths and every wrapping stack pointer are covered. This starts
AFTER the ground routine's animation/friction work. It is not a full-frame theorem
or a proof of NES/PPU support. The WP adapter shows how a caller can reuse the
bounded result without unfolding the instruction interpreter.
-/
open Smb Smb.Routine Std.WP Lean.Order
set_option experimental.vcgen true
set_option linter.unusedVariables false
open Smb.Routine.MemoryContracts

attribute [local irreducible] mphRam
namespace Smb.Routine.GroundScroll

-- Match sym_run's normalized stack offsets using the imported preservation theorem.
theorem mph_stack_off (ram : UInt16 → UInt8) (sp k₁ k₂ : UInt8)
    (h : (k₁ != k₂) = true) :
    mphRam (sp + k₁) ram ((256 ||| (sp + k₂).toUInt16) &&& 2047) =
      ram ((256 ||| (sp + k₂).toUInt16) &&& 2047) := by
  simp only [bne_iff_ne, ne_eq] at h
  apply mphRam_preserves <;> (try simp only [stackCell]) <;> bv_decide

theorem mph_stack_base (ram : UInt16 → UInt8) (sp k : UInt8)
    (h : (k != 0) = true) :
    mphRam (sp + k) ram ((256 ||| sp.toUInt16) &&& 2047) =
      ram ((256 ||| sp.toUInt16) &&& 2047) := by
  simp only [bne_iff_ne, ne_eq] at h
  apply mphRam_preserves <;> (try simp only [stackCell]) <;> bv_decide

theorem mph_speed (sp : UInt8) (ram : UInt16 → UInt8) :
    mphRam sp ram 0x57 = ram 0x57 := (mphRam_caller sp ram).1

theorem mph_facing (sp : UInt8) (ram : UInt16 → UInt8) :
    mphRam sp ram 0x33 = ram 0x33 := (mphRam_caller sp ram).2.1


-- Exactly the JSR / STA suffix of OnGroundStateSub, plus its final RTS.
def callerCode : List UInt8 := smbPrg% 0xB366 7

def scrollValue (ram : UInt16 → UInt8) : UInt8 :=
  bif ram 0x70E == 0 then mphCarry ram + mphHi (ram 0x57) else ram 0x70E

def ScrollPost (s₀ t : Plain) : Prop :=
  t.regs.pc = 0xB36C ∧ t.bad = false ∧ t.regs.s = s₀.regs.s ∧
  t.ram 0x6FF = scrollValue s₀.ram ∧ t.regs.a = scrollValue s₀.ram ∧
  t.ram 0x57 = s₀.ram 0x57 ∧ t.ram 0x33 = s₀.ram 0x33 ∧
  t.cyc = s₀.cyc + (bif s₀.ram 0x70E == 0 then
    (bif s₀.ram 0x57 ≥ 0x80 then 125 else 123) else 23)

-- 54 = JSR (1) + the callee theorem's 50 + continuation reserve (3).
-- With m=0, reusing the theorem leaves j+3. RTS and STA consume two;
-- the stop lemma applies to j+1. General m adds m to these budgets.
-- No bound on existential j is assumed; symbolic m also avoids the literal-fuel matcher issue.
-- The arbitrary initial stack pointer includes wraparound at 0 and 1.
set_option maxHeartbeats 2000000 in
theorem actual_call (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcaller : CodeAt prg 0x3366 callerCode)
    (hcallee : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hI : (p &&& 4 == 0) = false) :
    let s₀ : Plain := ⟨⟨0xB366,a,x,y,sp,p⟩,ram,prg,cyc,false⟩
    ScrollPost s₀ ((CPU.runTo (σ := Plain) 0xB36C (m + 54)).run s₀).2 := by
  dsimp only
  have hrts : prg 0x3F4C = 0x60 := by
    have h := hcallee
    simp only [CodeAt, movePlayerHorizontallyCode, moveObjectHorizontallyCode,
      List.cons_append, List.nil_append, UInt16.reduceAdd] at h
    simp [h]
  simp only [CodeAt, callerCode, UInt16.reduceAdd] at hcaller
  generalize hrun : ((CPU.runTo (σ := Plain) 0xB36C (m + 54)).run
    ⟨⟨0xB366,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = f
  sym_run hrun [hcaller, hrts, hI, mph_stack_off, mph_stack_base] calls [movePlayerHorizontally_call]
  all_goals
    intros
    clear hcaller hrts hcallee
    simp only [ScrollPost, scrollValue, mphCarry, mphHi, mphLo, mph_speed, mph_facing] at *
    bv_decide

-- Match the proved run without unfolding the interpreter into the WP goal.
attribute [local irreducible] CPU.runTo

def CallPre (s : Plain) : Prop :=
  s.regs.pc = 0xB366 ∧ s.bad = false ∧
  CodeAt s.prg 0x3366 callerCode ∧
  CodeAt s.prg 0x3F09 movePlayerHorizontallyCode ∧ (s.regs.p &&& 4 == 0) = false

@[spec] theorem actual_call_spec (s₀ : Plain) :
    ⦃fun s => s = s₀ ∧ CallPre s₀⦄ CPU.runTo (σ := Plain) 0xB36C 54
    ⦃fun _ t => ScrollPost s₀ t⦄ := by
  constructor
  intro s hs
  rcases hs with ⟨hs,h⟩
  subst s
  rcases s₀ with ⟨⟨pc,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩
  rcases h with ⟨hpc,hbad,hcaller,hcallee,hI⟩
  dsimp only at hpc hbad hcaller hcallee hI
  subst pc
  subst bad
  exact actual_call 0 a x y sp p ram prg cyc hcaller hcallee hI

@[spec] theorem getRegs_spec (post : Regs → Plain → Prop) :
    ⦃fun s => post s.regs s⦄ CPU.getRegs (σ := Plain) ⦃post⦄ := ⟨fun _ h => h⟩

-- The underlying program above now includes an actual JSR, RTS and caller STA.
-- vcgen uses only its relational contract; it does not inspect callee instructions.
theorem caller_observe (s₀ : Plain) :
    ⦃fun s => s = s₀ ∧ CallPre s₀⦄
    (do CPU.runTo 0xB36C 54; CPU.getRegs : StateM Plain Regs)
    ⦃fun r t => r.pc = 0xB36C ∧ r.s = s₀.regs.s ∧
      t.ram 0x6FF = scrollValue s₀.ram ∧ t.bad = false⦄ := by
  vcgen
  all_goals grind [ScrollPost]

theorem caller_rom : CodeAt (fun a => Smb.prg.get! (a &&& 0x7FFF).toNat) 0x3366 callerCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem callee_rom : CodeAt (fun a => Smb.prg.get! (a &&& 0x7FFF).toNat) 0x3F09 movePlayerHorizontallyCode :=
  codeAt_of_matches _ _ _ (by native_decide)

end Smb.Routine.GroundScroll
