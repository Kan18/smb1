import Smb.StepLemmas
import Smb.Abs.Sem
import Smb.SymRun
import Smb.Routine.ValueSetCertificate
open Smb Smb.Abs
namespace Smb.Abs
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# The pure instruction semantics agrees with the plain machine

`step_eval`: for each opcode `Smb.Abs.decode` knows, in ROM, with the I flag staying set and the accesses in range,
`CPU.step` gives exactly the registers and RAM writes of `Smb.Abs.eval`, leaves `prg` alone and does not set `bad`.
-/

/-- RAM after `Eff.wr`'s writes, in order. -/
def applyW (ram : UInt16 → UInt8) : List (UInt16 × UInt8) → UInt16 → UInt8
  | [], i => ram i
  | (a, b) :: l, i => applyW (fun i => bif i == a &&& 0x7FF then b else ram i) l i

/-- What one instruction does on the plain machine. -/
def StepOk (s t : Plain) (e : Eff) : Prop :=
  t.regs = e.regs ∧ t.prg = s.prg ∧ t.ram = applyW s.ram e.wr ∧ t.bad = s.bad

abbrev mr (s : Plain) := Plain.memRead s.ram s.prg
def b1Of (s : Plain) : UInt8 := s.prg (s.regs.pc + 1 &&& 0x7FFF)
def b2Of (s : Plain) : UInt8 := s.prg (s.regs.pc + 2 &&& 0x7FFF)
def loOf (s : Plain) (k : Kind) : UInt8 := mr s (ptrAddrs k (b1Of s) (b2Of s) s.regs).1
def hiOf (s : Plain) (k : Kind) : UInt8 := mr s (ptrAddrs k (b1Of s) (b2Of s) s.regs).2
def vOf (s : Plain) (k : Kind) : UInt8 := mr s (operandAddr k (b1Of s) (b2Of s) s.regs (loOf s k) (hiOf s k))
def evalS (s : Plain) (k : Kind) : Eff := eval k (b1Of s) (b2Of s) s.regs (loOf s k) (hiOf s k) (vOf s k)

theorem pfst {α β : Type} (a : α) (b : β) : (a, b).1 = a := rfl
theorem psnd {α β : Type} (a : α) (b : β) : (a, b).2 = b := rfl

theorem lt8192_false (b : UInt16) (h : 0x8000 ≤ b) : decide (b < 8192) = false := by
  simp only [decide_eq_false_iff_not]; bv_decide (config := { enums := false })
theorem ge32768_true (b : UInt16) (h : 0x8000 ≤ b) : decide (32768 ≤ b) = true := by
  simp only [decide_eq_true_eq]; exact h

theorem u8_lt (b : UInt8) : decide (b.toUInt16 < 8192) = true := by
  simp only [decide_eq_true_eq]; bv_decide (config := { enums := false })
theorem stk_lt (b : UInt8) : decide ((256 ||| b.toUInt16) < 8192) = true := by
  simp only [decide_eq_true_eq]; bv_decide (config := { enums := false })

set_option hygiene false in
macro "eval_finish" : tactic => `(tactic| (
  and_intros
  all_goals first
    | rfl
    | trivial
    | (funext i; bv_decide (config := { enums := false }))
    | bv_decide (config := { enums := false })
    | (fun_congr; bv_decide (config := { enums := false }))))

set_option hygiene false in
macro "eval_tac" tail:ident opv:term "," kd:term : tactic => `(tactic| (
  obtain ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ := s
  simp only at h0 h2 hop hi
  have h1 : (0x8000 : UInt16) ≤ pc + 1 := by bv_decide (config := { enums := false })
  have h3 : (0x8000 : UInt16) ≤ pc + 2 := by bv_decide (config := { enums := false })
  have e2 : pc + 1 + 1 = pc + 2 := by bv_decide (config := { enums := false })
  have hk : decode $opv = $kd := by decide
  simp only [StepOk, ValueSets.step_eq, ValueSets.memRead_rom ram prg pc h0, hop, ValueSets.readable_rom pc h0,
    Bool.not_true, Bool.or_false]
  rw [show ($opv : UInt8) = $opv from rfl, $tail:ident]
  simp only [hk] at hok hi' ⊢
  simp only [evalS, loOf, hiOf, vOf, b1Of, b2Of, mr, ptrAddrs, operandAddr, ptrCells, eval, ea, Mode.size, accessOk, base,
    regOf, stack, relTarget, aluFn, shiftFn, nz, applyW, Plain.memRead, Plain.inRam, ↓reduceIte, reduceCtorEq, CPU.FC, CPU.FZ, CPU.FN, CPU.FV, CPU.FB, CPU.FU] at hok hi' ⊢
  simp only [lt8192_false _ h1, ge32768_true _ h1, e2, lt8192_false _ h3, ge32768_true _ h3, Bool.cond_false, Bool.false_or, Bool.not_true, Bool.or_false, Regs.mk.injEq, u8_lt, stk_lt, Bool.cond_true, Bool.true_or] at hok hi' ⊢
  (try simp only [pfst, psnd, Regs.mk.injEq, u8_lt, stk_lt, Bool.cond_true, bne] at hi' ⊢)
  eval_finish))

theorem cond_snd {α β : Type} (c : Bool) (a b : α × β) : (cond c a b).2 = cond c a.2 b.2 := by cases c <;> rfl
theorem cond_regs (c : Bool) (a b : Plain) : (cond c a b).regs = cond c a.regs b.regs := by cases c <;> rfl
theorem cond_ram (c : Bool) (a b : Plain) : (cond c a b).ram = cond c a.ram b.ram := by cases c <;> rfl
theorem cond_prg (c : Bool) (a b : Plain) : (cond c a b).prg = cond c a.prg b.prg := by cases c <;> rfl
theorem cond_bad (c : Bool) (a b : Plain) : (cond c a b).bad = cond c a.bad b.bad := by cases c <;> rfl

set_option hygiene false in
macro "eval_tac_br" tail:ident opv:term "," kd:term "," mk:term : tactic => `(tactic| (
  obtain ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ := s
  simp only at h0 h2 hop hi
  have h1 : (0x8000 : UInt16) ≤ pc + 1 := by bv_decide (config := { enums := false })
  have h3 : (0x8000 : UInt16) ≤ pc + 2 := by bv_decide (config := { enums := false })
  have e2 : pc + 1 + 1 = pc + 2 := by bv_decide (config := { enums := false })
  have hk : decode $opv = $kd := by decide
  simp only [StepOk, ValueSets.step_eq, ValueSets.memRead_rom ram prg pc h0, hop, ValueSets.readable_rom pc h0,
    Bool.not_true, Bool.or_false]
  rw [show ($opv : UInt8) = $opv from rfl, $tail:ident]
  simp only [hk] at hok hi' ⊢
  simp only [evalS, loOf, hiOf, vOf, b1Of, b2Of, mr, ptrAddrs, operandAddr, ptrCells, eval, ea, Mode.size, accessOk, base,
    regOf, stack, relTarget, aluFn, shiftFn, nz, applyW, Plain.memRead, Plain.inRam, ↓reduceIte, reduceCtorEq, CPU.FC, CPU.FZ, CPU.FN, CPU.FV, CPU.FB, CPU.FU] at hok hi' ⊢
  simp only [lt8192_false _ h1, ge32768_true _ h1, e2, lt8192_false _ h3, ge32768_true _ h3, Bool.cond_false, Bool.false_or, Bool.not_true, Bool.or_false, Regs.mk.injEq, u8_lt, stk_lt, Bool.cond_true, Bool.true_or] at hok hi' ⊢
  simp only [cond_snd, cond_regs, cond_ram, cond_prg, cond_bad, Bool.cond_self, Regs.mk.injEq]
  cases hc : (p &&& $mk != 0) <;>
    simp only [hc, Bool.cond_true, Bool.cond_false, Bool.not_true, Bool.not_false, cond_snd, cond_regs, cond_ram, cond_prg, cond_bad, Bool.cond_self, Regs.mk.injEq, beq_self_eq_true, Bool.true_eq, Bool.false_eq, reduceIte, ↓reduceIte] at hok hi' ⊢ <;>
    simp only [bne] at hc hok hi' ⊢ <;> eval_finish))

theorem t_a9 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 169) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 169) (b1Of s) (b2Of s) s.regs (loOf s (decode 169)) (hiOf s (decode 169)) = true)
    (hi' : (evalS s (decode 169)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 169)) := by
  eval_tac StepLemma.tail_a9 169, Kind.load .a .imm

theorem t_a5 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 165) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 165) (b1Of s) (b2Of s) s.regs (loOf s (decode 165)) (hiOf s (decode 165)) = true)
    (hi' : (evalS s (decode 165)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 165)) := by
  eval_tac StepLemma.tail_a5 165, Kind.load .a .zp

theorem t_b5 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 181) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 181) (b1Of s) (b2Of s) s.regs (loOf s (decode 181)) (hiOf s (decode 181)) = true)
    (hi' : (evalS s (decode 181)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 181)) := by
  eval_tac StepLemma.tail_b5 181, Kind.load .a .zpx

theorem t_ad (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 173) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 173) (b1Of s) (b2Of s) s.regs (loOf s (decode 173)) (hiOf s (decode 173)) = true)
    (hi' : (evalS s (decode 173)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 173)) := by
  eval_tac StepLemma.tail_ad 173, Kind.load .a .abs

theorem t_bd (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 189) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 189) (b1Of s) (b2Of s) s.regs (loOf s (decode 189)) (hiOf s (decode 189)) = true)
    (hi' : (evalS s (decode 189)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 189)) := by
  eval_tac StepLemma.tail_bd 189, Kind.load .a .absx

theorem t_b9 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 185) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 185) (b1Of s) (b2Of s) s.regs (loOf s (decode 185)) (hiOf s (decode 185)) = true)
    (hi' : (evalS s (decode 185)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 185)) := by
  eval_tac StepLemma.tail_b9 185, Kind.load .a .absy

theorem t_b1 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 177) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 177) (b1Of s) (b2Of s) s.regs (loOf s (decode 177)) (hiOf s (decode 177)) = true)
    (hi' : (evalS s (decode 177)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 177)) := by
  eval_tac StepLemma.tail_b1 177, Kind.load .a .indy

theorem t_a2 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 162) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 162) (b1Of s) (b2Of s) s.regs (loOf s (decode 162)) (hiOf s (decode 162)) = true)
    (hi' : (evalS s (decode 162)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 162)) := by
  eval_tac StepLemma.tail_a2 162, Kind.load .x .imm

theorem t_a6 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 166) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 166) (b1Of s) (b2Of s) s.regs (loOf s (decode 166)) (hiOf s (decode 166)) = true)
    (hi' : (evalS s (decode 166)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 166)) := by
  eval_tac StepLemma.tail_a6 166, Kind.load .x .zp

theorem t_b6 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 182) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 182) (b1Of s) (b2Of s) s.regs (loOf s (decode 182)) (hiOf s (decode 182)) = true)
    (hi' : (evalS s (decode 182)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 182)) := by
  eval_tac StepLemma.tail_b6 182, Kind.load .x .zpy

theorem t_ae (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 174) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 174) (b1Of s) (b2Of s) s.regs (loOf s (decode 174)) (hiOf s (decode 174)) = true)
    (hi' : (evalS s (decode 174)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 174)) := by
  eval_tac StepLemma.tail_ae 174, Kind.load .x .abs

theorem t_be (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 190) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 190) (b1Of s) (b2Of s) s.regs (loOf s (decode 190)) (hiOf s (decode 190)) = true)
    (hi' : (evalS s (decode 190)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 190)) := by
  eval_tac StepLemma.tail_be 190, Kind.load .x .absy

theorem t_a0 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 160) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 160) (b1Of s) (b2Of s) s.regs (loOf s (decode 160)) (hiOf s (decode 160)) = true)
    (hi' : (evalS s (decode 160)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 160)) := by
  eval_tac StepLemma.tail_a0 160, Kind.load .y .imm

theorem t_a4 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 164) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 164) (b1Of s) (b2Of s) s.regs (loOf s (decode 164)) (hiOf s (decode 164)) = true)
    (hi' : (evalS s (decode 164)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 164)) := by
  eval_tac StepLemma.tail_a4 164, Kind.load .y .zp

theorem t_b4 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 180) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 180) (b1Of s) (b2Of s) s.regs (loOf s (decode 180)) (hiOf s (decode 180)) = true)
    (hi' : (evalS s (decode 180)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 180)) := by
  eval_tac StepLemma.tail_b4 180, Kind.load .y .zpx

theorem t_ac (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 172) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 172) (b1Of s) (b2Of s) s.regs (loOf s (decode 172)) (hiOf s (decode 172)) = true)
    (hi' : (evalS s (decode 172)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 172)) := by
  eval_tac StepLemma.tail_ac 172, Kind.load .y .abs

theorem t_bc (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 188) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 188) (b1Of s) (b2Of s) s.regs (loOf s (decode 188)) (hiOf s (decode 188)) = true)
    (hi' : (evalS s (decode 188)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 188)) := by
  eval_tac StepLemma.tail_bc 188, Kind.load .y .absx

theorem t_85 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 133) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 133) (b1Of s) (b2Of s) s.regs (loOf s (decode 133)) (hiOf s (decode 133)) = true)
    (hi' : (evalS s (decode 133)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 133)) := by
  eval_tac StepLemma.tail_85 133, Kind.store .a .zp

theorem t_95 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 149) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 149) (b1Of s) (b2Of s) s.regs (loOf s (decode 149)) (hiOf s (decode 149)) = true)
    (hi' : (evalS s (decode 149)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 149)) := by
  eval_tac StepLemma.tail_95 149, Kind.store .a .zpx

theorem t_8d (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 141) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 141) (b1Of s) (b2Of s) s.regs (loOf s (decode 141)) (hiOf s (decode 141)) = true)
    (hi' : (evalS s (decode 141)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 141)) := by
  eval_tac StepLemma.tail_8d 141, Kind.store .a .abs

theorem t_9d (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 157) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 157) (b1Of s) (b2Of s) s.regs (loOf s (decode 157)) (hiOf s (decode 157)) = true)
    (hi' : (evalS s (decode 157)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 157)) := by
  eval_tac StepLemma.tail_9d 157, Kind.store .a .absx

theorem t_99 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 153) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 153) (b1Of s) (b2Of s) s.regs (loOf s (decode 153)) (hiOf s (decode 153)) = true)
    (hi' : (evalS s (decode 153)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 153)) := by
  eval_tac StepLemma.tail_99 153, Kind.store .a .absy

theorem t_91 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 145) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 145) (b1Of s) (b2Of s) s.regs (loOf s (decode 145)) (hiOf s (decode 145)) = true)
    (hi' : (evalS s (decode 145)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 145)) := by
  eval_tac StepLemma.tail_91 145, Kind.store .a .indy

theorem t_86 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 134) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 134) (b1Of s) (b2Of s) s.regs (loOf s (decode 134)) (hiOf s (decode 134)) = true)
    (hi' : (evalS s (decode 134)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 134)) := by
  eval_tac StepLemma.tail_86 134, Kind.store .x .zp

theorem t_8e (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 142) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 142) (b1Of s) (b2Of s) s.regs (loOf s (decode 142)) (hiOf s (decode 142)) = true)
    (hi' : (evalS s (decode 142)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 142)) := by
  eval_tac StepLemma.tail_8e 142, Kind.store .x .abs

theorem t_84 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 132) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 132) (b1Of s) (b2Of s) s.regs (loOf s (decode 132)) (hiOf s (decode 132)) = true)
    (hi' : (evalS s (decode 132)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 132)) := by
  eval_tac StepLemma.tail_84 132, Kind.store .y .zp

theorem t_94 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 148) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 148) (b1Of s) (b2Of s) s.regs (loOf s (decode 148)) (hiOf s (decode 148)) = true)
    (hi' : (evalS s (decode 148)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 148)) := by
  eval_tac StepLemma.tail_94 148, Kind.store .y .zpx

theorem t_8c (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 140) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 140) (b1Of s) (b2Of s) s.regs (loOf s (decode 140)) (hiOf s (decode 140)) = true)
    (hi' : (evalS s (decode 140)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 140)) := by
  eval_tac StepLemma.tail_8c 140, Kind.store .y .abs

theorem t_09 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 9) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 9) (b1Of s) (b2Of s) s.regs (loOf s (decode 9)) (hiOf s (decode 9)) = true)
    (hi' : (evalS s (decode 9)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 9)) := by
  eval_tac StepLemma.tail_09 9, Kind.alu 0 .imm

theorem t_05 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 5) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 5) (b1Of s) (b2Of s) s.regs (loOf s (decode 5)) (hiOf s (decode 5)) = true)
    (hi' : (evalS s (decode 5)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 5)) := by
  eval_tac StepLemma.tail_05 5, Kind.alu 0 .zp

theorem t_15 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 21) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 21) (b1Of s) (b2Of s) s.regs (loOf s (decode 21)) (hiOf s (decode 21)) = true)
    (hi' : (evalS s (decode 21)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 21)) := by
  eval_tac StepLemma.tail_15 21, Kind.alu 0 .zpx

theorem t_0d (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 13) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 13) (b1Of s) (b2Of s) s.regs (loOf s (decode 13)) (hiOf s (decode 13)) = true)
    (hi' : (evalS s (decode 13)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 13)) := by
  eval_tac StepLemma.tail_0d 13, Kind.alu 0 .abs

theorem t_1d (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 29) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 29) (b1Of s) (b2Of s) s.regs (loOf s (decode 29)) (hiOf s (decode 29)) = true)
    (hi' : (evalS s (decode 29)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 29)) := by
  eval_tac StepLemma.tail_1d 29, Kind.alu 0 .absx

theorem t_19 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 25) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 25) (b1Of s) (b2Of s) s.regs (loOf s (decode 25)) (hiOf s (decode 25)) = true)
    (hi' : (evalS s (decode 25)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 25)) := by
  eval_tac StepLemma.tail_19 25, Kind.alu 0 .absy

theorem t_29 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 41) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 41) (b1Of s) (b2Of s) s.regs (loOf s (decode 41)) (hiOf s (decode 41)) = true)
    (hi' : (evalS s (decode 41)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 41)) := by
  eval_tac StepLemma.tail_29 41, Kind.alu 1 .imm

theorem t_25 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 37) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 37) (b1Of s) (b2Of s) s.regs (loOf s (decode 37)) (hiOf s (decode 37)) = true)
    (hi' : (evalS s (decode 37)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 37)) := by
  eval_tac StepLemma.tail_25 37, Kind.alu 1 .zp

theorem t_2d (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 45) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 45) (b1Of s) (b2Of s) s.regs (loOf s (decode 45)) (hiOf s (decode 45)) = true)
    (hi' : (evalS s (decode 45)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 45)) := by
  eval_tac StepLemma.tail_2d 45, Kind.alu 1 .abs

theorem t_3d (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 61) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 61) (b1Of s) (b2Of s) s.regs (loOf s (decode 61)) (hiOf s (decode 61)) = true)
    (hi' : (evalS s (decode 61)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 61)) := by
  eval_tac StepLemma.tail_3d 61, Kind.alu 1 .absx

theorem t_39 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 57) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 57) (b1Of s) (b2Of s) s.regs (loOf s (decode 57)) (hiOf s (decode 57)) = true)
    (hi' : (evalS s (decode 57)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 57)) := by
  eval_tac StepLemma.tail_39 57, Kind.alu 1 .absy

theorem t_49 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 73) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 73) (b1Of s) (b2Of s) s.regs (loOf s (decode 73)) (hiOf s (decode 73)) = true)
    (hi' : (evalS s (decode 73)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 73)) := by
  eval_tac StepLemma.tail_49 73, Kind.alu 2 .imm

theorem t_45 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 69) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 69) (b1Of s) (b2Of s) s.regs (loOf s (decode 69)) (hiOf s (decode 69)) = true)
    (hi' : (evalS s (decode 69)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 69)) := by
  eval_tac StepLemma.tail_45 69, Kind.alu 2 .zp

theorem t_69 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 105) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 105) (b1Of s) (b2Of s) s.regs (loOf s (decode 105)) (hiOf s (decode 105)) = true)
    (hi' : (evalS s (decode 105)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 105)) := by
  eval_tac StepLemma.tail_69 105, Kind.alu 3 .imm

theorem t_65 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 101) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 101) (b1Of s) (b2Of s) s.regs (loOf s (decode 101)) (hiOf s (decode 101)) = true)
    (hi' : (evalS s (decode 101)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 101)) := by
  eval_tac StepLemma.tail_65 101, Kind.alu 3 .zp

theorem t_75 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 117) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 117) (b1Of s) (b2Of s) s.regs (loOf s (decode 117)) (hiOf s (decode 117)) = true)
    (hi' : (evalS s (decode 117)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 117)) := by
  eval_tac StepLemma.tail_75 117, Kind.alu 3 .zpx

theorem t_6d (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 109) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 109) (b1Of s) (b2Of s) s.regs (loOf s (decode 109)) (hiOf s (decode 109)) = true)
    (hi' : (evalS s (decode 109)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 109)) := by
  eval_tac StepLemma.tail_6d 109, Kind.alu 3 .abs

theorem t_7d (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 125) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 125) (b1Of s) (b2Of s) s.regs (loOf s (decode 125)) (hiOf s (decode 125)) = true)
    (hi' : (evalS s (decode 125)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 125)) := by
  eval_tac StepLemma.tail_7d 125, Kind.alu 3 .absx

theorem t_79 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 121) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 121) (b1Of s) (b2Of s) s.regs (loOf s (decode 121)) (hiOf s (decode 121)) = true)
    (hi' : (evalS s (decode 121)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 121)) := by
  eval_tac StepLemma.tail_79 121, Kind.alu 3 .absy

theorem t_c9 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 201) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 201) (b1Of s) (b2Of s) s.regs (loOf s (decode 201)) (hiOf s (decode 201)) = true)
    (hi' : (evalS s (decode 201)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 201)) := by
  eval_tac StepLemma.tail_c9 201, Kind.alu 6 .imm

theorem t_c5 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 197) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 197) (b1Of s) (b2Of s) s.regs (loOf s (decode 197)) (hiOf s (decode 197)) = true)
    (hi' : (evalS s (decode 197)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 197)) := by
  eval_tac StepLemma.tail_c5 197, Kind.alu 6 .zp

theorem t_d5 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 213) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 213) (b1Of s) (b2Of s) s.regs (loOf s (decode 213)) (hiOf s (decode 213)) = true)
    (hi' : (evalS s (decode 213)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 213)) := by
  eval_tac StepLemma.tail_d5 213, Kind.alu 6 .zpx

theorem t_cd (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 205) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 205) (b1Of s) (b2Of s) s.regs (loOf s (decode 205)) (hiOf s (decode 205)) = true)
    (hi' : (evalS s (decode 205)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 205)) := by
  eval_tac StepLemma.tail_cd 205, Kind.alu 6 .abs

theorem t_dd (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 221) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 221) (b1Of s) (b2Of s) s.regs (loOf s (decode 221)) (hiOf s (decode 221)) = true)
    (hi' : (evalS s (decode 221)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 221)) := by
  eval_tac StepLemma.tail_dd 221, Kind.alu 6 .absx

theorem t_d9 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 217) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 217) (b1Of s) (b2Of s) s.regs (loOf s (decode 217)) (hiOf s (decode 217)) = true)
    (hi' : (evalS s (decode 217)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 217)) := by
  eval_tac StepLemma.tail_d9 217, Kind.alu 6 .absy

theorem t_e9 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 233) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 233) (b1Of s) (b2Of s) s.regs (loOf s (decode 233)) (hiOf s (decode 233)) = true)
    (hi' : (evalS s (decode 233)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 233)) := by
  eval_tac StepLemma.tail_e9 233, Kind.alu 7 .imm

theorem t_e5 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 229) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 229) (b1Of s) (b2Of s) s.regs (loOf s (decode 229)) (hiOf s (decode 229)) = true)
    (hi' : (evalS s (decode 229)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 229)) := by
  eval_tac StepLemma.tail_e5 229, Kind.alu 7 .zp

theorem t_f5 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 245) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 245) (b1Of s) (b2Of s) s.regs (loOf s (decode 245)) (hiOf s (decode 245)) = true)
    (hi' : (evalS s (decode 245)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 245)) := by
  eval_tac StepLemma.tail_f5 245, Kind.alu 7 .zpx

theorem t_ed (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 237) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 237) (b1Of s) (b2Of s) s.regs (loOf s (decode 237)) (hiOf s (decode 237)) = true)
    (hi' : (evalS s (decode 237)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 237)) := by
  eval_tac StepLemma.tail_ed 237, Kind.alu 7 .abs

theorem t_fd (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 253) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 253) (b1Of s) (b2Of s) s.regs (loOf s (decode 253)) (hiOf s (decode 253)) = true)
    (hi' : (evalS s (decode 253)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 253)) := by
  eval_tac StepLemma.tail_fd 253, Kind.alu 7 .absx

theorem t_f9 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 249) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 249) (b1Of s) (b2Of s) s.regs (loOf s (decode 249)) (hiOf s (decode 249)) = true)
    (hi' : (evalS s (decode 249)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 249)) := by
  eval_tac StepLemma.tail_f9 249, Kind.alu 7 .absy

theorem t_e0 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 224) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 224) (b1Of s) (b2Of s) s.regs (loOf s (decode 224)) (hiOf s (decode 224)) = true)
    (hi' : (evalS s (decode 224)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 224)) := by
  eval_tac StepLemma.tail_e0 224, Kind.cmp .x .imm

theorem t_e4 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 228) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 228) (b1Of s) (b2Of s) s.regs (loOf s (decode 228)) (hiOf s (decode 228)) = true)
    (hi' : (evalS s (decode 228)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 228)) := by
  eval_tac StepLemma.tail_e4 228, Kind.cmp .x .zp

theorem t_c0 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 192) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 192) (b1Of s) (b2Of s) s.regs (loOf s (decode 192)) (hiOf s (decode 192)) = true)
    (hi' : (evalS s (decode 192)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 192)) := by
  eval_tac StepLemma.tail_c0 192, Kind.cmp .y .imm

theorem t_c4 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 196) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 196) (b1Of s) (b2Of s) s.regs (loOf s (decode 196)) (hiOf s (decode 196)) = true)
    (hi' : (evalS s (decode 196)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 196)) := by
  eval_tac StepLemma.tail_c4 196, Kind.cmp .y .zp

theorem t_cc (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 204) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 204) (b1Of s) (b2Of s) s.regs (loOf s (decode 204)) (hiOf s (decode 204)) = true)
    (hi' : (evalS s (decode 204)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 204)) := by
  eval_tac StepLemma.tail_cc 204, Kind.cmp .y .abs

theorem t_24 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 36) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 36) (b1Of s) (b2Of s) s.regs (loOf s (decode 36)) (hiOf s (decode 36)) = true)
    (hi' : (evalS s (decode 36)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 36)) := by
  eval_tac StepLemma.tail_24 36, Kind.bit .zp

theorem t_2c (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 44) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 44) (b1Of s) (b2Of s) s.regs (loOf s (decode 44)) (hiOf s (decode 44)) = true)
    (hi' : (evalS s (decode 44)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 44)) := by
  eval_tac StepLemma.tail_2c 44, Kind.bit .abs

theorem t_0e (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 14) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 14) (b1Of s) (b2Of s) s.regs (loOf s (decode 14)) (hiOf s (decode 14)) = true)
    (hi' : (evalS s (decode 14)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 14)) := by
  eval_tac StepLemma.tail_0e 14, Kind.rmw 0 .abs

theorem t_46 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 70) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 70) (b1Of s) (b2Of s) s.regs (loOf s (decode 70)) (hiOf s (decode 70)) = true)
    (hi' : (evalS s (decode 70)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 70)) := by
  eval_tac StepLemma.tail_46 70, Kind.rmw 1 .zp

theorem t_4e (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 78) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 78) (b1Of s) (b2Of s) s.regs (loOf s (decode 78)) (hiOf s (decode 78)) = true)
    (hi' : (evalS s (decode 78)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 78)) := by
  eval_tac StepLemma.tail_4e 78, Kind.rmw 1 .abs

theorem t_26 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 38) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 38) (b1Of s) (b2Of s) s.regs (loOf s (decode 38)) (hiOf s (decode 38)) = true)
    (hi' : (evalS s (decode 38)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 38)) := by
  eval_tac StepLemma.tail_26 38, Kind.rmw 2 .zp

theorem t_2e (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 46) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 46) (b1Of s) (b2Of s) s.regs (loOf s (decode 46)) (hiOf s (decode 46)) = true)
    (hi' : (evalS s (decode 46)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 46)) := by
  eval_tac StepLemma.tail_2e 46, Kind.rmw 2 .abs

theorem t_7e (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 126) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 126) (b1Of s) (b2Of s) s.regs (loOf s (decode 126)) (hiOf s (decode 126)) = true)
    (hi' : (evalS s (decode 126)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 126)) := by
  eval_tac StepLemma.tail_7e 126, Kind.rmw 3 .absx

theorem t_e6 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 230) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 230) (b1Of s) (b2Of s) s.regs (loOf s (decode 230)) (hiOf s (decode 230)) = true)
    (hi' : (evalS s (decode 230)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 230)) := by
  eval_tac StepLemma.tail_e6 230, Kind.rmw 4 .zp

theorem t_f6 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 246) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 246) (b1Of s) (b2Of s) s.regs (loOf s (decode 246)) (hiOf s (decode 246)) = true)
    (hi' : (evalS s (decode 246)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 246)) := by
  eval_tac StepLemma.tail_f6 246, Kind.rmw 4 .zpx

theorem t_ee (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 238) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 238) (b1Of s) (b2Of s) s.regs (loOf s (decode 238)) (hiOf s (decode 238)) = true)
    (hi' : (evalS s (decode 238)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 238)) := by
  eval_tac StepLemma.tail_ee 238, Kind.rmw 4 .abs

theorem t_fe (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 254) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 254) (b1Of s) (b2Of s) s.regs (loOf s (decode 254)) (hiOf s (decode 254)) = true)
    (hi' : (evalS s (decode 254)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 254)) := by
  eval_tac StepLemma.tail_fe 254, Kind.rmw 4 .absx

theorem t_c6 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 198) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 198) (b1Of s) (b2Of s) s.regs (loOf s (decode 198)) (hiOf s (decode 198)) = true)
    (hi' : (evalS s (decode 198)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 198)) := by
  eval_tac StepLemma.tail_c6 198, Kind.rmw 5 .zp

theorem t_d6 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 214) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 214) (b1Of s) (b2Of s) s.regs (loOf s (decode 214)) (hiOf s (decode 214)) = true)
    (hi' : (evalS s (decode 214)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 214)) := by
  eval_tac StepLemma.tail_d6 214, Kind.rmw 5 .zpx

theorem t_ce (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 206) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 206) (b1Of s) (b2Of s) s.regs (loOf s (decode 206)) (hiOf s (decode 206)) = true)
    (hi' : (evalS s (decode 206)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 206)) := by
  eval_tac StepLemma.tail_ce 206, Kind.rmw 5 .abs

theorem t_de (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 222) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 222) (b1Of s) (b2Of s) s.regs (loOf s (decode 222)) (hiOf s (decode 222)) = true)
    (hi' : (evalS s (decode 222)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 222)) := by
  eval_tac StepLemma.tail_de 222, Kind.rmw 5 .absx

theorem t_0a (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 10) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 10) (b1Of s) (b2Of s) s.regs (loOf s (decode 10)) (hiOf s (decode 10)) = true)
    (hi' : (evalS s (decode 10)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 10)) := by
  eval_tac StepLemma.tail_0a 10, Kind.shiftA 0

theorem t_4a (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 74) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 74) (b1Of s) (b2Of s) s.regs (loOf s (decode 74)) (hiOf s (decode 74)) = true)
    (hi' : (evalS s (decode 74)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 74)) := by
  eval_tac StepLemma.tail_4a 74, Kind.shiftA 1

theorem t_2a (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 42) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 42) (b1Of s) (b2Of s) s.regs (loOf s (decode 42)) (hiOf s (decode 42)) = true)
    (hi' : (evalS s (decode 42)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 42)) := by
  eval_tac StepLemma.tail_2a 42, Kind.shiftA 2

theorem t_6a (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 106) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 106) (b1Of s) (b2Of s) s.regs (loOf s (decode 106)) (hiOf s (decode 106)) = true)
    (hi' : (evalS s (decode 106)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 106)) := by
  eval_tac StepLemma.tail_6a 106, Kind.shiftA 3

theorem t_e8 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 232) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 232) (b1Of s) (b2Of s) s.regs (loOf s (decode 232)) (hiOf s (decode 232)) = true)
    (hi' : (evalS s (decode 232)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 232)) := by
  eval_tac StepLemma.tail_e8 232, Kind.incdec .x 1

theorem t_ca (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 202) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 202) (b1Of s) (b2Of s) s.regs (loOf s (decode 202)) (hiOf s (decode 202)) = true)
    (hi' : (evalS s (decode 202)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 202)) := by
  eval_tac StepLemma.tail_ca 202, Kind.incdec .x 0xFF

theorem t_c8 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 200) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 200) (b1Of s) (b2Of s) s.regs (loOf s (decode 200)) (hiOf s (decode 200)) = true)
    (hi' : (evalS s (decode 200)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 200)) := by
  eval_tac StepLemma.tail_c8 200, Kind.incdec .y 1

theorem t_88 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 136) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 136) (b1Of s) (b2Of s) s.regs (loOf s (decode 136)) (hiOf s (decode 136)) = true)
    (hi' : (evalS s (decode 136)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 136)) := by
  eval_tac StepLemma.tail_88 136, Kind.incdec .y 0xFF

theorem t_aa (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 170) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 170) (b1Of s) (b2Of s) s.regs (loOf s (decode 170)) (hiOf s (decode 170)) = true)
    (hi' : (evalS s (decode 170)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 170)) := by
  eval_tac StepLemma.tail_aa 170, Kind.xfer .a .x

theorem t_8a (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 138) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 138) (b1Of s) (b2Of s) s.regs (loOf s (decode 138)) (hiOf s (decode 138)) = true)
    (hi' : (evalS s (decode 138)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 138)) := by
  eval_tac StepLemma.tail_8a 138, Kind.xfer .x .a

theorem t_a8 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 168) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 168) (b1Of s) (b2Of s) s.regs (loOf s (decode 168)) (hiOf s (decode 168)) = true)
    (hi' : (evalS s (decode 168)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 168)) := by
  eval_tac StepLemma.tail_a8 168, Kind.xfer .a .y

theorem t_98 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 152) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 152) (b1Of s) (b2Of s) s.regs (loOf s (decode 152)) (hiOf s (decode 152)) = true)
    (hi' : (evalS s (decode 152)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 152)) := by
  eval_tac StepLemma.tail_98 152, Kind.xfer .y .a

theorem t_9a (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 154) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 154) (b1Of s) (b2Of s) s.regs (loOf s (decode 154)) (hiOf s (decode 154)) = true)
    (hi' : (evalS s (decode 154)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 154)) := by
  eval_tac StepLemma.tail_9a 154, Kind.txs

theorem t_18 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 24) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 24) (b1Of s) (b2Of s) s.regs (loOf s (decode 24)) (hiOf s (decode 24)) = true)
    (hi' : (evalS s (decode 24)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 24)) := by
  eval_tac StepLemma.tail_18 24, Kind.setp 1 0

theorem t_38 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 56) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 56) (b1Of s) (b2Of s) s.regs (loOf s (decode 56)) (hiOf s (decode 56)) = true)
    (hi' : (evalS s (decode 56)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 56)) := by
  eval_tac StepLemma.tail_38 56, Kind.setp 0 1

theorem t_78 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 120) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 120) (b1Of s) (b2Of s) s.regs (loOf s (decode 120)) (hiOf s (decode 120)) = true)
    (hi' : (evalS s (decode 120)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 120)) := by
  eval_tac StepLemma.tail_78 120, Kind.setp 0 4

theorem t_d8 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 216) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 216) (b1Of s) (b2Of s) s.regs (loOf s (decode 216)) (hiOf s (decode 216)) = true)
    (hi' : (evalS s (decode 216)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 216)) := by
  eval_tac StepLemma.tail_d8 216, Kind.setp 8 0

theorem t_10 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 16) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 16) (b1Of s) (b2Of s) s.regs (loOf s (decode 16)) (hiOf s (decode 16)) = true)
    (hi' : (evalS s (decode 16)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 16)) := by
  eval_tac_br StepLemma.tail_10 16, Kind.branch 0x80 false, 0x80

theorem t_30 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 48) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 48) (b1Of s) (b2Of s) s.regs (loOf s (decode 48)) (hiOf s (decode 48)) = true)
    (hi' : (evalS s (decode 48)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 48)) := by
  eval_tac_br StepLemma.tail_30 48, Kind.branch 0x80 true, 0x80

theorem t_90 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 144) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 144) (b1Of s) (b2Of s) s.regs (loOf s (decode 144)) (hiOf s (decode 144)) = true)
    (hi' : (evalS s (decode 144)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 144)) := by
  eval_tac_br StepLemma.tail_90 144, Kind.branch 1 false, 1

theorem t_b0 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 176) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 176) (b1Of s) (b2Of s) s.regs (loOf s (decode 176)) (hiOf s (decode 176)) = true)
    (hi' : (evalS s (decode 176)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 176)) := by
  eval_tac_br StepLemma.tail_b0 176, Kind.branch 1 true, 1

theorem t_d0 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 208) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 208) (b1Of s) (b2Of s) s.regs (loOf s (decode 208)) (hiOf s (decode 208)) = true)
    (hi' : (evalS s (decode 208)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 208)) := by
  eval_tac_br StepLemma.tail_d0 208, Kind.branch 2 false, 2

theorem t_f0 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 240) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 240) (b1Of s) (b2Of s) s.regs (loOf s (decode 240)) (hiOf s (decode 240)) = true)
    (hi' : (evalS s (decode 240)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 240)) := by
  eval_tac_br StepLemma.tail_f0 240, Kind.branch 2 true, 2

theorem t_4c (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 76) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 76) (b1Of s) (b2Of s) s.regs (loOf s (decode 76)) (hiOf s (decode 76)) = true)
    (hi' : (evalS s (decode 76)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 76)) := by
  eval_tac StepLemma.tail_4c 76, Kind.jmp

theorem t_6c (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 108) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 108) (b1Of s) (b2Of s) s.regs (loOf s (decode 108)) (hiOf s (decode 108)) = true)
    (hi' : (evalS s (decode 108)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 108)) := by
  eval_tac StepLemma.tail_6c 108, Kind.jmpi

theorem t_20 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 32) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 32) (b1Of s) (b2Of s) s.regs (loOf s (decode 32)) (hiOf s (decode 32)) = true)
    (hi' : (evalS s (decode 32)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 32)) := by
  eval_tac StepLemma.tail_20 32, Kind.jsr

theorem t_60 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 96) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 96) (b1Of s) (b2Of s) s.regs (loOf s (decode 96)) (hiOf s (decode 96)) = true)
    (hi' : (evalS s (decode 96)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 96)) := by
  eval_tac StepLemma.tail_60 96, Kind.rts

theorem t_40 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 64) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 64) (b1Of s) (b2Of s) s.regs (loOf s (decode 64)) (hiOf s (decode 64)) = true)
    (hi' : (evalS s (decode 64)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 64)) := by
  eval_tac StepLemma.tail_40 64, Kind.rti

theorem t_48 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 72) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 72) (b1Of s) (b2Of s) s.regs (loOf s (decode 72)) (hiOf s (decode 72)) = true)
    (hi' : (evalS s (decode 72)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 72)) := by
  eval_tac StepLemma.tail_48 72, Kind.pha

theorem t_68 (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 104) (hi : s.regs.p &&& 4 ≠ 0)
    (hok : accessOk (decode 104) (b1Of s) (b2Of s) s.regs (loOf s (decode 104)) (hiOf s (decode 104)) = true)
    (hi' : (evalS s (decode 104)).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode 104)) := by
  eval_tac StepLemma.tail_68 104, Kind.pla

def knownOps : List UInt8 := [169, 165, 181, 173, 189, 185, 177, 162, 166, 182, 174, 190, 160, 164, 180, 172, 188, 133, 149, 141, 157, 153, 145, 134, 142, 132, 148, 140, 9, 5, 21, 13, 29, 25, 41, 37, 45, 61, 57, 73, 69, 105, 101, 117, 109, 125, 121, 201, 197, 213, 205, 221, 217, 233, 229, 245, 237, 253, 249, 224, 228, 192, 196, 204, 36, 44, 14, 70, 78, 38, 46, 126, 230, 246, 238, 254, 198, 214, 206, 222, 10, 74, 42, 106, 232, 202, 200, 136, 170, 138, 168, 152, 154, 24, 56, 120, 216, 16, 48, 144, 176, 208, 240, 76, 108, 32, 96, 64, 72, 104]

/-- `decode` knows exactly these opcodes. -/
theorem decode_known (op : UInt8) (h : decode op ≠ .unknown) : op ∈ knownOps := by
  have key : ∀ n : Fin 256, decode (UInt8.ofNat n.val) ≠ .unknown → UInt8.ofNat n.val ∈ knownOps := by decide
  have := key ⟨op.toNat, op.toNat_lt⟩
  simpa using this (by simpa using h)

/-- One instruction of the game's code on the plain machine is `eval` on the values it reads. -/
theorem step_eval (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0) (hi : s.regs.p &&& 4 ≠ 0)
    (hk : decode (s.prg (s.regs.pc &&& 0x7FFF)) ≠ .unknown)
    (hok : accessOk (decode (s.prg (s.regs.pc &&& 0x7FFF))) (b1Of s) (b2Of s) s.regs
      (loOf s (decode (s.prg (s.regs.pc &&& 0x7FFF)))) (hiOf s (decode (s.prg (s.regs.pc &&& 0x7FFF)))) = true)
    (hi' : (evalS s (decode (s.prg (s.regs.pc &&& 0x7FFF)))).regs.p &&& 4 ≠ 0) :
    StepOk s (CPU.step.run s).2 (evalS s (decode (s.prg (s.regs.pc &&& 0x7FFF)))) := by
  generalize hop : s.prg (s.regs.pc &&& 0x7FFF) = op at *
  have hm := decode_known op hk
  simp only [knownOps, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact t_a9 s h0 h2 hop hi hok hi'
  · exact t_a5 s h0 h2 hop hi hok hi'
  · exact t_b5 s h0 h2 hop hi hok hi'
  · exact t_ad s h0 h2 hop hi hok hi'
  · exact t_bd s h0 h2 hop hi hok hi'
  · exact t_b9 s h0 h2 hop hi hok hi'
  · exact t_b1 s h0 h2 hop hi hok hi'
  · exact t_a2 s h0 h2 hop hi hok hi'
  · exact t_a6 s h0 h2 hop hi hok hi'
  · exact t_b6 s h0 h2 hop hi hok hi'
  · exact t_ae s h0 h2 hop hi hok hi'
  · exact t_be s h0 h2 hop hi hok hi'
  · exact t_a0 s h0 h2 hop hi hok hi'
  · exact t_a4 s h0 h2 hop hi hok hi'
  · exact t_b4 s h0 h2 hop hi hok hi'
  · exact t_ac s h0 h2 hop hi hok hi'
  · exact t_bc s h0 h2 hop hi hok hi'
  · exact t_85 s h0 h2 hop hi hok hi'
  · exact t_95 s h0 h2 hop hi hok hi'
  · exact t_8d s h0 h2 hop hi hok hi'
  · exact t_9d s h0 h2 hop hi hok hi'
  · exact t_99 s h0 h2 hop hi hok hi'
  · exact t_91 s h0 h2 hop hi hok hi'
  · exact t_86 s h0 h2 hop hi hok hi'
  · exact t_8e s h0 h2 hop hi hok hi'
  · exact t_84 s h0 h2 hop hi hok hi'
  · exact t_94 s h0 h2 hop hi hok hi'
  · exact t_8c s h0 h2 hop hi hok hi'
  · exact t_09 s h0 h2 hop hi hok hi'
  · exact t_05 s h0 h2 hop hi hok hi'
  · exact t_15 s h0 h2 hop hi hok hi'
  · exact t_0d s h0 h2 hop hi hok hi'
  · exact t_1d s h0 h2 hop hi hok hi'
  · exact t_19 s h0 h2 hop hi hok hi'
  · exact t_29 s h0 h2 hop hi hok hi'
  · exact t_25 s h0 h2 hop hi hok hi'
  · exact t_2d s h0 h2 hop hi hok hi'
  · exact t_3d s h0 h2 hop hi hok hi'
  · exact t_39 s h0 h2 hop hi hok hi'
  · exact t_49 s h0 h2 hop hi hok hi'
  · exact t_45 s h0 h2 hop hi hok hi'
  · exact t_69 s h0 h2 hop hi hok hi'
  · exact t_65 s h0 h2 hop hi hok hi'
  · exact t_75 s h0 h2 hop hi hok hi'
  · exact t_6d s h0 h2 hop hi hok hi'
  · exact t_7d s h0 h2 hop hi hok hi'
  · exact t_79 s h0 h2 hop hi hok hi'
  · exact t_c9 s h0 h2 hop hi hok hi'
  · exact t_c5 s h0 h2 hop hi hok hi'
  · exact t_d5 s h0 h2 hop hi hok hi'
  · exact t_cd s h0 h2 hop hi hok hi'
  · exact t_dd s h0 h2 hop hi hok hi'
  · exact t_d9 s h0 h2 hop hi hok hi'
  · exact t_e9 s h0 h2 hop hi hok hi'
  · exact t_e5 s h0 h2 hop hi hok hi'
  · exact t_f5 s h0 h2 hop hi hok hi'
  · exact t_ed s h0 h2 hop hi hok hi'
  · exact t_fd s h0 h2 hop hi hok hi'
  · exact t_f9 s h0 h2 hop hi hok hi'
  · exact t_e0 s h0 h2 hop hi hok hi'
  · exact t_e4 s h0 h2 hop hi hok hi'
  · exact t_c0 s h0 h2 hop hi hok hi'
  · exact t_c4 s h0 h2 hop hi hok hi'
  · exact t_cc s h0 h2 hop hi hok hi'
  · exact t_24 s h0 h2 hop hi hok hi'
  · exact t_2c s h0 h2 hop hi hok hi'
  · exact t_0e s h0 h2 hop hi hok hi'
  · exact t_46 s h0 h2 hop hi hok hi'
  · exact t_4e s h0 h2 hop hi hok hi'
  · exact t_26 s h0 h2 hop hi hok hi'
  · exact t_2e s h0 h2 hop hi hok hi'
  · exact t_7e s h0 h2 hop hi hok hi'
  · exact t_e6 s h0 h2 hop hi hok hi'
  · exact t_f6 s h0 h2 hop hi hok hi'
  · exact t_ee s h0 h2 hop hi hok hi'
  · exact t_fe s h0 h2 hop hi hok hi'
  · exact t_c6 s h0 h2 hop hi hok hi'
  · exact t_d6 s h0 h2 hop hi hok hi'
  · exact t_ce s h0 h2 hop hi hok hi'
  · exact t_de s h0 h2 hop hi hok hi'
  · exact t_0a s h0 h2 hop hi hok hi'
  · exact t_4a s h0 h2 hop hi hok hi'
  · exact t_2a s h0 h2 hop hi hok hi'
  · exact t_6a s h0 h2 hop hi hok hi'
  · exact t_e8 s h0 h2 hop hi hok hi'
  · exact t_ca s h0 h2 hop hi hok hi'
  · exact t_c8 s h0 h2 hop hi hok hi'
  · exact t_88 s h0 h2 hop hi hok hi'
  · exact t_aa s h0 h2 hop hi hok hi'
  · exact t_8a s h0 h2 hop hi hok hi'
  · exact t_a8 s h0 h2 hop hi hok hi'
  · exact t_98 s h0 h2 hop hi hok hi'
  · exact t_9a s h0 h2 hop hi hok hi'
  · exact t_18 s h0 h2 hop hi hok hi'
  · exact t_38 s h0 h2 hop hi hok hi'
  · exact t_78 s h0 h2 hop hi hok hi'
  · exact t_d8 s h0 h2 hop hi hok hi'
  · exact t_10 s h0 h2 hop hi hok hi'
  · exact t_30 s h0 h2 hop hi hok hi'
  · exact t_90 s h0 h2 hop hi hok hi'
  · exact t_b0 s h0 h2 hop hi hok hi'
  · exact t_d0 s h0 h2 hop hi hok hi'
  · exact t_f0 s h0 h2 hop hi hok hi'
  · exact t_4c s h0 h2 hop hi hok hi'
  · exact t_6c s h0 h2 hop hi hok hi'
  · exact t_20 s h0 h2 hop hi hok hi'
  · exact t_60 s h0 h2 hop hi hok hi'
  · exact t_40 s h0 h2 hop hi hok hi'
  · exact t_48 s h0 h2 hop hi hok hi'
  · exact t_68 s h0 h2 hop hi hok hi'

end Smb.Abs
