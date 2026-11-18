import Smb.Routine.AbsCheck

/-!
# A run that leaves a checked region leaves through its exit

A region's checked table keeps its invariant along any run until the exit (`inv_runTo`), but doesn't say the exit is
reached. When a later stop `B` has no box in the table, a run that does reach `B` must have left the region first, and
the only way out is the exit `A`. So the run to `B` is the run to `A`, then a run to `B` from a state at `A` that the
invariant describes. That's what lets an opaque region sit inside a longer summary: the code after it starts from that
state, whatever RAM the region left within its bounds.
-/
namespace Smb.Abs

theorem runTo_zero (stop : UInt16) (s : Plain) : ((CPU.runTo (σ := Plain) stop 0).run s).2 = s := rfl

theorem runTo_at (stop : UInt16) (n : Nat) (s : Plain) (h : s.regs.pc = stop) :
    ((CPU.runTo (σ := Plain) stop n).run s).2 = s := by
  cases n with
  | zero => rfl
  | succ n =>
    have hregs : Bus.regs s = s.regs := rfl
    simp only [CPU.runTo, CPU.getRegs, hregs, h, ↓reduceIte, bind, StateT.bind, pure, StateT.pure, StateT.run]

theorem runTo_succ (stop : UInt16) (n : Nat) (s : Plain) (h : s.regs.pc ≠ stop) :
    ((CPU.runTo (σ := Plain) stop (n + 1)).run s).2 = ((CPU.runTo (σ := Plain) stop n).run (CPU.step.run s).2).2 := by
  have hregs : Bus.regs s = s.regs := rfl
  simp only [CPU.runTo, CPU.getRegs, hregs, h, ↓reduceIte, bind, StateT.bind, StateT.run]
  cases he : CPU.step s with
  | mk u t => rfl

/-- **Through the exit.** A run to `B` from inside a checked region with exit `A`, where `B` has no box, that does
reach `B`, is a run to `B` from some state at `A` inside the invariant. -/
theorem runTo_through {rom : UInt16 → UInt8} {exit prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    (hchk : check rom exit prot g T = true) (htop : gAt g 0x300 = .top) (htop2 : gAt g 0x340 = .top)
    (A B : UInt16) (hexit : ∀ a, exit a = true → a = A) (hB : T.at B = []) :
    ∀ (n : Nat) (s : Plain), Code rom s → Inv prot g ram0 T s → ((CPU.runTo (σ := Plain) B n).run s).2.regs.pc = B →
      ∃ k u, u.regs.pc = A ∧ Code rom u ∧ Inv prot g ram0 T u ∧
        ((CPU.runTo (σ := Plain) B n).run s).2 = ((CPU.runTo (σ := Plain) B k).run u).2 := by
  have hnotB : ∀ s : Plain, Inv prot g ram0 T s → s.regs.pc ≠ B := by
    intro s ⟨b, hb, _⟩ heq
    rw [heq, hB] at hb
    exact absurd hb (List.not_mem_nil)
  intro n
  induction n with
  | zero =>
    intro s _ hi hp
    rw [runTo_zero] at hp
    exact absurd hp (hnotB s hi)
  | succ n ih =>
    intro s hc hi hp
    by_cases hA : s.regs.pc = A
    · exact ⟨n + 1, s, hA, hc, hi, rfl⟩
    · have hx : exit s.regs.pc = false := by
        cases he : exit s.regs.pc with
        | false => rfl
        | true => exact absurd (hexit _ he) hA
      have hs := inv_step hchk hc hi hx (assumedOk_of_top htop htop2 _)
      rw [runTo_succ B n s (hnotB s hi)] at hp ⊢
      exact ih _ hs.1 hs.2 hp

/-- As `runTo_through`, for a region with several exits: the run leaves through one of them. -/
theorem runTo_through_exit {rom : UInt16 → UInt8} {exit prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    (hchk : check rom exit prot g T = true) (htop : gAt g 0x300 = .top) (htop2 : gAt g 0x340 = .top)
    (B : UInt16) (hB : T.at B = []) :
    ∀ (n : Nat) (s : Plain), Code rom s → Inv prot g ram0 T s → ((CPU.runTo (σ := Plain) B n).run s).2.regs.pc = B →
      ∃ k u, exit u.regs.pc = true ∧ Code rom u ∧ Inv prot g ram0 T u ∧
        ((CPU.runTo (σ := Plain) B n).run s).2 = ((CPU.runTo (σ := Plain) B k).run u).2 := by
  have hnotB : ∀ s : Plain, Inv prot g ram0 T s → s.regs.pc ≠ B := by
    intro s ⟨b, hb, _⟩ heq
    rw [heq, hB] at hb
    exact absurd hb (List.not_mem_nil)
  intro n
  induction n with
  | zero =>
    intro s _ hi hp
    rw [runTo_zero] at hp
    exact absurd hp (hnotB s hi)
  | succ n ih =>
    intro s hc hi hp
    cases hx : exit s.regs.pc with
    | true => exact ⟨n + 1, s, hx, hc, hi, rfl⟩
    | false =>
      have hs := inv_step hchk hc hi hx (assumedOk_of_top htop htop2 _)
      rw [runTo_succ B n s (hnotB s hi)] at hp ⊢
      exact ih _ hs.1 hs.2 hp

/-- A run to a region's exit `A`, where its only other exit is `D`: it ends inside the invariant, or it passed `D` first,
from a state inside the invariant. -/
theorem runTo_two_exits {rom : UInt16 → UInt8} {exit prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    (hchk : check rom exit prot g T = true) (htop : gAt g 0x300 = .top) (htop2 : gAt g 0x340 = .top)
    (A D : UInt16) (hexit : ∀ a, exit a = true → a = A ∨ a = D) :
    ∀ (n : Nat) (s : Plain), Code rom s → Inv prot g ram0 T s →
      (Code rom ((CPU.runTo (σ := Plain) A n).run s).2 ∧ Inv prot g ram0 T ((CPU.runTo (σ := Plain) A n).run s).2) ∨
      ∃ k u, u.regs.pc = D ∧ Code rom u ∧ Inv prot g ram0 T u ∧
        ((CPU.runTo (σ := Plain) A n).run s).2 = ((CPU.runTo (σ := Plain) A k).run u).2 := by
  intro n
  induction n with
  | zero => intro s hc hi; exact Or.inl ⟨hc, hi⟩
  | succ n ih =>
    intro s hc hi
    by_cases hA : s.regs.pc = A
    · rw [runTo_at A _ s hA]; exact Or.inl ⟨hc, hi⟩
    · by_cases hD : s.regs.pc = D
      · exact Or.inr ⟨n + 1, s, hD, hc, hi, rfl⟩
      · have hx : exit s.regs.pc = false := by
          cases he : exit s.regs.pc with
          | false => rfl
          | true =>
            rcases hexit _ he with h | h
            · exact absurd h hA
            · exact absurd h hD
        have hs := inv_step hchk hc hi hx (assumedOk_of_top htop htop2 _)
        rw [runTo_succ A n s hA]
        exact ih _ hs.1 hs.2

end Smb.Abs
