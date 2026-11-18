import Smb.Routine.PpuFrame

/-! The model-error flag is sticky under every CPU bus operation. -/
namespace Smb.Sticky
open Smb.NES Smb.Routine.PpuFrame CPU

theorem pure {α : Type} (a : α) : UF (Pure.pure a : StateM NES α) := fun _ h => h

theorem bind {α β : Type} {m : StateM NES α} {f : α → StateM NES β}
    (hm : UF m) (hf : ∀ a, UF (f a)) : UF (m >>= f) := by
  intro s h
  rw [Sim.run_bind] at h
  exact hm s (hf _ _ h)

theorem ite {α : Type} {c : Prop} [Decidable c] {a b : StateM NES α}
    (ha : c → UF a) (hb : ¬c → UF b) : UF (if c then a else b) := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; exact ha h
  · simp only [h, ↓reduceIte]; exact hb h

theorem getRegs : UF (getRegs (σ := NES)) := fun _ h => h
theorem modRegs (f : Regs → Regs) : UF (modRegs (σ := NES) f) := fun _ h => h
theorem rd (a : UInt16) : UF (rd (σ := NES) a) := uf_rd a
theorem wr (a : UInt16) (b : UInt8) : UF (wr (σ := NES) a b) :=
  uf_of fun s h => wrS_mono s a b h
theorem idle : UF (idle (σ := NES)) :=
  uf_of fun s h => end_mono _ (begin_mono s h)
theorem unsupported : UF (unsupported (σ := NES)) := by
  intro s h
  cases h
theorem nmiPending : UF (nmiPending (σ := NES)) := fun _ h => h
theorem clearNmiPending : UF (clearNmiPending (σ := NES)) := fun _ h => h
theorem nmiPolled : UF (nmiPolled (σ := NES)) := fun _ h => h
theorem setNmiPolled (b : Bool) : UF (setNmiPolled (σ := NES) b) := fun _ h => h

syntax "sticky_tac" : tactic
macro_rules
  | `(tactic| sticky_tac) => `(tactic| (
      sim_unfold
      repeat' (first
        | with_reducible exact Sticky.getRegs | with_reducible exact Sticky.modRegs _
        | with_reducible exact Sticky.rd _ | with_reducible exact Sticky.wr _ _
        | with_reducible exact Sticky.idle | with_reducible exact Sticky.unsupported
        | with_reducible exact Sticky.clearNmiPending | with_reducible exact Sticky.pure _
        | with_reducible exact Sticky.setNmiPolled _ | with_reducible exact Sticky.nmiPending | with_reducible exact Sticky.nmiPolled
        | with_reducible refine Sticky.bind ?_ (fun _ => ?_)
        | with_reducible refine Sticky.ite (fun _ => ?_) (fun _ => ?_)
        | split
        | dsimp only
        | simp only [Bool.or_self, Bool.false_or, Bool.or_false])))

end Smb.Sticky
