import Smb.RefineExec
import Smb.Run

/-!
# Refinement for whole instructions and runs

`Sim.step`: one `CPU.step` (instruction plus interrupt checks) on the full NES simulates the
plain machine; `Sim.runTo`: so does running to a stop address. `NES.toPlain` is the plain
view of a full state, and `refine_runTo` packages the result: if the plain run of a routine
is not `bad`, the full NES run ends with the same CPU registers, RAM and cycle count.
-/
namespace Smb

namespace Sim

theorem fetch : Sim (CPU.fetch (σ := NES)) (CPU.fetch (σ := Plain)) := by sim_tac

theorem stepTail (op : UInt8) : Sim (CPU.stepTail (σ := NES) op) (CPU.stepTail (σ := Plain) op) := by
  unfold CPU.stepTail
  refine Sim.bind (exec op) (fun _ => ?_)
  sim_tac

theorem step : Sim (CPU.step (σ := NES)) (CPU.step (σ := Plain)) := by
  unfold CPU.step
  exact Sim.bind fetch stepTail

theorem runTo (stop : UInt16) (n : Nat) :
    Sim (CPU.runTo (σ := NES) stop n) (CPU.runTo (σ := Plain) stop n) := by
  induction n with
  | zero => exact Sim.pure ()
  | succ n ih =>
    simp only [CPU.runTo]
    refine Sim.bind Sim.getRegs (fun _ => ?_)
    exact Sim.ite (fun _ => Sim.pure ()) (fun _ => Sim.bind step (fun _ => ih))

end Sim

/-- The plain-machine view of a full NES state. -/
def NES.toPlain (s : NES) : Plain :=
  ⟨⟨s.pc, s.a, s.x, s.y, s.s, s.p⟩, fun i => s.ram.get! (i &&& 0x7FF).toNat,
   fun a => s.prg.get! (a &&& 0x7FFF).toNat, s.cyc, false⟩

theorem and_idem (i m : UInt16) : (i &&& m) &&& m = i &&& m := by bv_decide

/-- The conditions under which CPU code on the full NES behaves like the plain machine. -/
structure NES.Quiet (s : NES) : Prop where
  size : s.ram.size = 0x800
  nmiOff : s.ctrl &&& 0x80 = 0
  noNmi : s.nmiPending = false
  noPoll : s.nmiPolled = false
  noDma : s.dmaPending = false

theorem NES.rel_toPlain (s : NES) (h : s.Quiet) : Rel s s.toPlain :=
  { regs := rfl
    ram := fun i => by
      show s.ram.get! (i &&& 0x7FF).toNat = s.ram.get! ((i &&& 0x7FF) &&& 0x7FF).toNat
      rw [and_idem]
    size := h.size
    prg := fun a => by
      show s.prg.get! (a &&& 0x7FFF).toNat = s.prg.get! ((a &&& 0x7FFF) &&& 0x7FFF).toNat
      rw [and_idem]
    cyc := rfl, ctrl := h.nmiOff, nmiPending := h.noNmi, nmiPolled := h.noPoll, dma := h.noDma }

/-- If the plain run to `stop` from the plain view of a quiet NES state is not `bad`, the
full NES run ends with exactly the plain run's registers, RAM and cycle count (and is
still quiet). -/
theorem refine_runTo (s : NES) (h : s.Quiet) (stop : UInt16) (n : Nat)
    (hb : ((CPU.runTo (σ := Plain) stop n).run s.toPlain).2.bad = false) :
    Rel ((CPU.runTo (σ := NES) stop n).run s).2 ((CPU.runTo (σ := Plain) stop n).run s.toPlain).2 :=
  ((Sim.runTo stop n).2 s s.toPlain (NES.rel_toPlain s h) hb).2

end Smb
