import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# The frame rule's counter: one step of `IntervalTimerControl` (`$80F6`–`$810D`)

```
lda TimerControl; beq DecTimers; dec TimerControl; bne NoDecTimers
DecTimers: ldx #$14; dec IntervalTimerControl; bpl DecTimersLoop
           lda #$14; sta IntervalTimerControl; ldx #$23
DecTimersLoop: ...
```
With `TimerControl` 0 or 1 the counter steps, and on going negative reloads 20; X selects whether the
interval timers ($23) or only the frame timers ($14) decrement. Otherwise the counter is frozen.
Plain machine. Says nothing about whether the code runs on a frame (lag, pause).
-/
namespace Smb.Routine.FrameTiming

def timerCode : List UInt8 :=
  smbPrg% 0x80F6 24

def itcNext (c : UInt8) : UInt8 := bif (c - 1) &&& 0x80 != 0 then 0x14 else c - 1

def TimerSummary (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.bad = false ∧
  (ram 0x747 ≠ 0 → ram 0x747 ≠ 1 →
    t.regs.pc = 0x8119 ∧ t.ram 0x747 = ram 0x747 - 1 ∧ t.ram 0x77F = ram 0x77F) ∧
  (ram 0x747 = 0 ∨ ram 0x747 = 1 →
    t.regs.pc = 0x810E ∧ t.ram 0x747 = 0 ∧ t.ram 0x77F = itcNext (ram 0x77F) ∧
    t.regs.x = (bif ((ram 0x77F) - 1) &&& 0x80 != 0 then 0x23 else 0x14))

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem timerStep_reach (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x80F6 ≤ a && a ≤ 0x810E || a == 0x8119) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x00F6 timerCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 12)).run ⟨⟨0x80F6, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ TimerSummary ram t := by
  simp only [CodeAt, timerCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 12)).run ⟨⟨0x80F6, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hI] until [33038, 33049]
  all_goals
    intros
    clear hcode
    subst hrun
    reach_finish [TimerSummary, itcNext]

/-- Values 0..20 stay in range, and the counter has period 21 there. -/
theorem itcNext_range : ∀ i : Fin 21, (itcNext (UInt8.ofNat i.val)).toNat ≤ 20 := by decide

def itcIter : Nat → UInt8 → UInt8
  | 0, c => c
  | n + 1, c => itcIter n (itcNext c)

set_option maxRecDepth 100000 in
theorem itc_period : ∀ i : Fin 21, itcIter 21 (UInt8.ofNat i.val) = UInt8.ofNat i.val := by decide

set_option maxRecDepth 100000 in
/-- The counter reloads exactly once per 21 steps: from `c`, the reload is on step `c + 1`. -/
theorem itc_wrap_at : ∀ i : Fin 21, itcIter (i.val + 1) (UInt8.ofNat i.val) = 20 := by decide

#print axioms timerStep_reach
#print axioms itc_period

end Smb.Routine.FrameTiming
