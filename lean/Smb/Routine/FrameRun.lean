import Smb.Routine.FrameGuard

/-!
# The frame invariant across `NES.frame`

`FrameGuard` and `FrameClose` iterate `CPU.step` with the controller bytes fixed. A real run goes through `NES.frame`, which changes those bytes and resets `polls` and `frameDone` at each frame's
start. None of that touches what `FInv` reads, so `finv_run` carries `FInv` along `NES.runFrames` for any inputs.

The run's hypothesis, `RunClear`, says each instruction leaves `unmodelled` false and the run clean, and has no `done` address, which is what `finv_stepN` asks of each step. That the flag can't be cleared once set isn't proved, so a
frame's end doesn't by itself give that for the instructions inside it.
-/
namespace Smb.Routine.FrameRun
open Smb NES Smb.Abs Smb.Routine.PpuFrame Smb.Routine.FrameGuard

/-- What a frame changes at its start. -/
def startFrame (p0 p1 : UInt8) (s : NES) : NES := { s with pad0 := p0, pad1 := p1, polls := 0, frameDone := false }

theorem frame_def (p0 p1 : UInt8) (s : NES) : NES.frame p0 p1 s = NES.frame.go NES.frameFuel (startFrame p0 p1 s) := rfl

theorem RelD_start {s : NES} {t : Plain} (p0 p1 : UInt8) (h : RelD s t) : RelD (startFrame p0 p1 s) t :=
  ⟨h.regs, h.ram, h.size, h.prg, h.ctrl, h.nmiPending, h.nmiPolled⟩

theorem RelOn_start {s : NES} {t : Plain} (p0 p1 : UInt8) (h : RelOn s t) : RelOn (startFrame p0 p1 s) t :=
  ⟨h.regs, h.ram, h.size, h.prg, h.dma⟩

theorem Calm_start {k : Nat} {s : NES} (p0 p1 : UInt8) (h : PpuCalm.Calm k s) : PpuCalm.Calm k (startFrame p0 p1 s) :=
  ⟨h.vbl, h.line, h.pending, h.next, h.near, h.on, h.dead, h.dma⟩

theorem ZStage_start {s : NES} (p0 p1 : UInt8) (h : ZStage s) : ZStage (startFrame p0 p1 s) := by
  have sv {x : NES} (hx : SchS x) : SchS (startFrame p0 p1 x) :=
    SchS.of_sv hx ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩
  have off {x : NES} (hx : OffBase x) : OffBase (startFrame p0 p1 x) := ⟨sv hx.sch, hx.off, hx.dma⟩
  have on {x : NES} (hx : OnBase x) : OnBase (startFrame p0 p1 x) := ⟨sv hx.sch, hx.on, hx.dma⟩
  obtain ⟨hp, h⟩ := h
  refine ⟨hp, ?_⟩
  rcases h with ⟨a, b, c, d⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨hp2, h⟩
  · exact Or.inl ⟨a, sv b, c, d⟩
  · exact Or.inr (Or.inl ⟨a, off b, c⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a, off b, c⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, off b, c, d⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, on b, c⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, on b, c⟩)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp2, ?_⟩)))))
    rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨a, Calm_start p0 p1 b⟩
    · exact Or.inr (Or.inl ⟨a, Calm_start p0 p1 b⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a, Calm_start p0 p1 b⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, Calm_start p0 p1 b⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, Calm_start p0 p1 b⟩)))

theorem finv_start {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z : Region} {s : NES} (p0 p1 : UInt8)
    (h : FInv rom g rs Z s) : FInv rom g rs Z (startFrame p0 p1 s) := by
  obtain ⟨hS, hP, r, hr, ram0, ⟨t, hc, hinv, hrel⟩, hz⟩ := h
  refine ⟨Sch.of_sv hS ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩, hP, r, hr, ram0, ⟨t, hc, hinv, ?_⟩, fun e => ?_⟩
  · rcases hrel with h1 | ⟨h2, h3⟩
    · exact Or.inl (RelD_start p0 p1 h1)
    · exact Or.inr ⟨h2, RelOn_start p0 p1 h3⟩
  · rcases hz e with h1 | h1
    · exact Or.inl (ZStage_start p0 p1 h1)
    · exact Or.inr h1

/-- Every instruction of the frame's loop leaves `unmodelled` false and the run clean, and has no `done` address. -/
def GoClear (g : Global) (done : UInt16 → Bool) : Nat → NES → Prop
  | 0, _ => True
  | n + 1, s => s.frameDone = true ∨ (done s.pc = false ∧ (CPU.step.run s).2.unmodelled = false ∧ Clean g (CPU.step.run s).2 ∧ GoClear g done n (CPU.step.run s).2)

theorem finv_go {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z : Region} {done : UInt16 → Bool}
    (hf : Fits rom g rs done) (hz : ZFits rs Z) (n : Nat) (s : NES) (h : FInv rom g rs Z s) (hus : s.unmodelled = false)
    (hc : GoClear g done n s) (hgo : (NES.frame.go n s).unmodelled = false) : FInv rom g rs Z (NES.frame.go n s) := by
  induction n generalizing s with
  | zero => simp [NES.frame.go] at hgo
  | succ n ih =>
    simp only [NES.frame.go] at hgo ⊢
    split
    · exact h
    · rename_i hfd
      simp only [hfd, if_false] at hgo
      rcases hc with hd | ⟨hd, hu, hA, hc⟩
      · exact absurd hd hfd
      · exact ih _ (finv_step hf hz h hd hus hu hA).2 hu hc hgo

/-- `inputs` stay in the model, and clear of `done`, frame by frame. -/
def RunClear (g : Global) (done : UInt16 → Bool) : List UInt8 → NES → Prop
  | [], _ => True
  | b :: l, s => GoClear g done NES.frameFuel (startFrame b 0 s) ∧ (NES.frame b 0 s).unmodelled = false ∧ RunClear g done l (NES.frame b 0 s)

/-- `FInv` along `NES.runFrames`, for any inputs and PPU timing. -/
theorem finv_run {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z : Region} {done : UInt16 → Bool}
    (hf : Fits rom g rs done) (hz : ZFits rs Z) (l : List UInt8) (s : NES) (h : FInv rom g rs Z s) (hus : s.unmodelled = false)
    (hc : RunClear g done l s) : FInv rom g rs Z (NES.runFrames l s) := by
  induction l generalizing s with
  | nil => exact h
  | cons b l ih =>
    obtain ⟨h1, h2, h3⟩ := hc
    exact ih _ (finv_go hf hz _ _ (finv_start b 0 h) hus h1 h2) h2 h3

end Smb.Routine.FrameRun
