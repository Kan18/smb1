import Smb.Routine.FrameGuard
import Smb.Routine.SavedRegions

/-! Remove the abstract interrupt guard for saved-memory region handoffs,
using the same checked closing sequence and PPU schedule as `FrameGuard`. -/
namespace Smb.Routine.FrameGuard
open Smb NES Smb.Abs Smb.Routine.PpuFrame

def SavedFInv (rom : UInt16 → UInt8) (g : Global) (rs : List Region) (Z : Region)
    (saved : Region → (UInt16 → UInt8) → Prop) (s : NES) : Prop :=
  Sch s ∧ s.prg = Smb.prg ∧ ∃ r ∈ rs, ∃ ram0,
    GInv rom r.prot g ram0 r.T s ∧ saved r ram0 ∧ (r = Z → ZStage s ∨ s.pc = 0x808F)

theorem savedFinv_step_region {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z : Region} {done : UInt16 → Bool} {saved : Region → (UInt16 → UInt8) → Prop} {s : NES}
    (hf : SavedFits rom g rs done saved) (hz : ZFits rs Z) (h : SavedFInv rom g rs Z saved s) (hd : done s.pc = false) (hus : s.unmodelled = false)
    (hu : (CPU.step.run s).2.unmodelled = false)
    (hA : (∀ i : UInt16, (∀ r ∈ rs, r.prot (i &&& 0x7FF) = true) → 0x200 ≤ i &&& 0x7FF → (CPU.step.run s).2.ram.get! (i &&& 0x7FF).toNat = s.ram.get! (i &&& 0x7FF).toNat) → Clean g (CPU.step.run s).2) :
    Guard s ∧ SavedFInv rom g rs Z saved (CPU.step.run s).2 ∧
      ∃ r1 ∈ rs, ∃ ram1, GInv rom r1.prot g ram1 r1.T s ∧ r1.exit s.pc = false ∧ GInv rom r1.prot g ram1 r1.T (CPU.step.run s).2 := by
  obtain ⟨hS, hP, r, hr, ram0, hi, hsaved, hzs⟩ := h
  have hSS : SchS s := by
    rcases hS with h | h
    · rw [hus] at h; cases h
    · exact h
  have key : ∃ r1 ∈ rs, ∃ ram1, GInv rom r1.prot g ram1 r1.T s ∧ r1.exit s.pc = false ∧ saved r1 ram1 ∧ (r1 = Z → ZStage s) := by
    cases hx : r.exit s.pc with
    | false =>
      refine ⟨r, hr, ram0, hi, hx, hsaved, fun e => ?_⟩
      rcases hzs e with h | h
      · exact h
      · subst e
        rw [h, hz.exit] at hx
        cases hx
    | true =>
      obtain ⟨t, hc, ⟨b, hbm, hb⟩, hrel⟩ := hi
      have hspc : s.pc = t.regs.pc := by
        rcases hrel with h1 | ⟨_, h1⟩
        · exact congrArg Regs.pc h1.regs
        · exact congrArg Regs.pc h1.regs
      rcases hf.link r hr ram0 b t hbm hb hsaved (by simpa [← hspc] using hx) with
        hd' | ⟨r', hr', q, hq, hx', hqhold, hsave'⟩
      · rw [← hspc, hd] at hd'; cases hd'
      · have hi' : GInv rom r'.prot g t.ram r'.T s :=
          ⟨t, hc, inv_of_entry (List.all_eq_true.mp (hf.entries r' hr') q hq) hqhold, hrel⟩
        refine ⟨r', hr', t.ram, hi', by simpa [hspc] using hx', hsave', fun e => ?_⟩
        have hq8 := hz.entries q (by simpa [e] using hq)
        have hpc : s.pc = 0x8178 := hspc.trans (hqhold.pc.trans hq8)
        rcases hrel with h1 | ⟨h2, _⟩
        · exact ⟨hP, Or.inl ⟨hpc, hSS, h1.ctrl, h1.nmiPending⟩⟩
        · rw [← hspc, hpc] at h2
          exact absurd h2 (by decide)
  obtain ⟨r1, hr1, ram1, hi1, hx1, hsave1, hz1⟩ := key
  have hstep : Guard s ∧ (r1 = Z → ZStage (CPU.step.run s).2 ∨ (CPU.step.run s).2.pc = 0x808F) := by
    by_cases e : r1 = Z
    · have zs := hz1 e
      have rti : s.pc = 0x8181 → (preChecks s).pc = 0x8057 := fun hpc =>
        ginv_rti_pc (hf.chk r1 hr1) hx1 hi1 hpc (zs_ctrl zs hpc)
      obtain ⟨g1, g2⟩ := zs_step zs hu rti
      exact ⟨g1, fun _ => g2⟩
    · refine ⟨?_, fun e' => absurd e' e⟩
      intro hg
      obtain ⟨t, hc, ⟨b, hbm, hb⟩, hrel⟩ := hi1
      have hspc : s.pc = t.regs.pc := by
        rcases hrel with h1 | ⟨_, h1⟩
        · exact congrArg Regs.pc h1.regs
        · exact congrArg Regs.pc h1.regs
      rw [hz.empty r1 hr1 e t.regs.pc (by rw [← hspc]; exact hg)] at hbm
      cases hbm
  have hnext := ginv_stepK (hf.chk r1 hr1) (hf.idle r1 hr1) hi1 hx1 hstep.1
    (fun hk => hA (fun i hi hl => (hk i (hi r1 hr1) hl).trans (ginv_ram hi1 i (hi r1 hr1)).symm))
  exact ⟨hstep.1, ⟨(Pres.step s).1 hS, by rw [(Pres.step s).2]; exact hP, r1, hr1, ram1, hnext, hsave1, hstep.2⟩, r1, hr1, ram1, hi1, hx1, hnext⟩

theorem savedFinv_stepN {rom : UInt16 → UInt8} {g : Global} {rs : List Region}
    {Z : Region} {done : UInt16 → Bool} {saved : Region → (UInt16 → UInt8) → Prop}
    (hf : SavedFits rom g rs done saved) (hz : ZFits rs Z) (n : Nat) (s : NES)
    (hd : ∀ i, i < n → done (stepN i s).pc = false)
    (hu : ∀ i, i ≤ n → (stepN i s).unmodelled = false)
    (hA : ∀ i, i < n → Clean g (stepN (i + 1) s))
    (h : SavedFInv rom g rs Z saved s) : SavedFInv rom g rs Z saved (stepN n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih =>
    exact ih (CPU.step.run s).2 (fun i hi => hd (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => hu (i + 1) (Nat.succ_le_succ hi))
      (fun i hi => hA (i + 1) (Nat.succ_lt_succ hi))
      (savedFinv_step_region hf hz h (hd 0 (Nat.succ_pos _))
        (hu 0 (Nat.zero_le _)) (hu 1 (by omega)) (fun _ => hA 0 (Nat.succ_pos _))).2.1

end Smb.Routine.FrameGuard
