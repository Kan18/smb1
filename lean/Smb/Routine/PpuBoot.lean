import Smb.Routine.PpuSchedExec
import Smb.Game
import Smb.Routine.AbsBridge

/-!
# The PPU's schedule on any run of the game

`PpuSched` shows each instruction keeps the event schedule, once it's well formed. Here the game's own runs reach it: at power-on the PPU ignores writes, so the schedule's invariant doesn't hold
yet, and the second frame ends with it holding. From then on `Sch` holds for every input. Since `Sch` allows `unmodelled = true`, this yields the well-formed schedule `SchS` only on supported runs; it does not establish supportedness.
-/
namespace Smb.Routine.PpuBoot
open Smb NES

/-- `SchS`, as a test. -/
def schB (s : NES) : Bool :=
  (s.evIdx == 0 || s.evIdx == 1 || s.evIdx == 2 || s.evIdx == 3 || s.evIdx == 4 || s.evIdx == 6 || s.evIdx == 7) &&
  decide (s.fpos ≤ phPos s s.evIdx) && decide (s.nextEv ≤ phPos s s.evIdx) &&
  (s.nextEv == phPos s s.evIdx || s.nextEv == s.hitPos || s.nextEv == s.overflowPos) &&
  decide (s.skipped ≤ 1) &&
  (!(s.evIdx == 4 || s.evIdx == 6 || s.evIdx == 7) || s.flen == 262 * 341 - s.skipped) &&
  (!(s.evIdx == 4 || s.evIdx == 6) || decide (s.line < 240)) &&
  (!(s.evIdx == 7 || s.evIdx == 0 || s.evIdx == 1 || s.evIdx == 2) || s.line == 240) &&
  (!(s.evIdx == 3) || s.line == 0) &&
  (!(s.evIdx == 0 || s.evIdx == 1) || (s.hitPos == NONE && s.overflowPos == NONE)) &&
  (!s.vbl || s.evIdx == 1) &&
  s.dead == 0 &&
  decide (s.fpos < phPos s s.evIdx)

theorem imp_of {a b : Bool} (h : (!a || b) = true) : a = true → b = true := by
  cases a <;> cases b <;> simp_all

theorem schB_sound {s : NES} (h : schB s = true) : SchS s := by
  simp only [schB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, i⟩, j⟩, k⟩, l⟩, m⟩, n⟩ := h
  refine { idx := ?_, le := of_decide_eq_true b, nle := of_decide_eq_true c, ncase := ?_, skip := of_decide_eq_true e, flen := ?_, lineL := ?_, line240 := ?_, line0 := ?_, none := ?_, vbl1 := ?_, dead := ?_, lt := of_decide_eq_true n }
  · simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using a
  · simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using d
  · intro hh
    have := imp_of f (by simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using hh)
    simpa using this
  · intro hh
    have := imp_of g (by simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using hh)
    exact of_decide_eq_true this
  · intro hh
    have := imp_of i (by simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using hh)
    simpa using this
  · intro hh
    have := imp_of j (by simpa using hh)
    simpa using this
  · intro hh
    have := imp_of k (by simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using hh)
    simpa using this
  · intro hh
    have := imp_of l hh
    simpa using this
  · simpa using m

theorem sch_go (n : Nat) (s : NES) (h : Sch s) : Sch (NES.frame.go n s) := by
  induction n generalizing s with
  | zero => exact Or.inl rfl
  | succ n ih =>
    simp only [NES.frame.go]
    split
    · exact h
    · exact ih _ ((Pres.step s).1 h)

theorem sch_frame (p0 p1 : UInt8) (s : NES) (h : Sch s) : Sch (NES.frame p0 p1 s) :=
  sch_go _ _ (Sch.of_sv h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩)

theorem rom_go (n : Nat) (s : NES) : (NES.frame.go n s).prg = s.prg := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [NES.frame.go]
    split
    · rfl
    · rw [ih, (Pres.step s).2]

/-- The schedule at the end of the second frame, for each pair of inputs. -/
def bootAll : Bool :=
  (List.range 256).all fun p =>
    let s := NES.frame (UInt8.ofNat p) 0 Smb.initial
    (List.range 256).all fun q => schB (NES.frame (UInt8.ofNat q) 0 s)

/-- At the end of the second frame the schedule is well formed, whatever the controller did. The PPU's power-on state ends in the first frame's pre-render line. -/
theorem boot_check : bootAll = true := by native_decide

theorem sch_first (p q : UInt8) : Sch (NES.frame q 0 (NES.frame p 0 Smb.initial)) := by
  have h := List.all_eq_true.mp (show _ = true from boot_check) p.toNat (List.mem_range.mpr p.toNat_lt)
  have h2 := List.all_eq_true.mp h q.toNat (List.mem_range.mpr q.toNat_lt)
  rw [UInt8.ofNat_toNat, UInt8.ofNat_toNat] at h2
  exact Or.inr (schB_sound h2)

theorem run_cons (a : UInt8) (l : List UInt8) (s : NES) : NES.runFrames (a :: l) s = NES.runFrames l (NES.frame a 0 s) := by
  simp only [NES.runFrames, List.foldl]

theorem sch_foldl (l : List UInt8) (s : NES) (h : Sch s) : Sch (NES.runFrames l s) := by
  induction l generalizing s with
  | nil => exact h
  | cons a l ih =>
    rw [run_cons]
    exact ih _ (sch_frame a 0 s h)

/-- After two frames, every run of the game has a well-formed schedule at each frame's end. -/
theorem sch_run (p q : UInt8) (l : List UInt8) : Sch (NES.runFrames (p :: q :: l) Smb.initial) := by
  rw [run_cons, run_cons]
  exact sch_foldl l _ (sch_first p q)

theorem rom_frame (p0 p1 : UInt8) (s : NES) : (NES.frame p0 p1 s).prg = s.prg := rom_go _ _

theorem rom_run (l : List UInt8) (s : NES) : (NES.runFrames l s).prg = s.prg := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    rw [run_cons, ih, rom_frame]

theorem sch_stepN (n : Nat) (s : NES) (h : Sch s) : Sch (Abs.stepN n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih _ ((Pres.step s).1 h)

end Smb.Routine.PpuBoot
