import Smb.Routine.SavedFrameGuard

/-!
# One step of a saved-region cycle, keeping track of the region

`savedFinv_step_region` says some region's invariant holds across a step, but not which. `savedFinv_step_track`
starts from a named region `r` and says the region across the step is `r` itself, or one `r` hands over to at this
instruction, entered at one of its entry boxes, at this address.
-/
namespace Smb.Routine.FrameGuard
open Smb NES Smb.Abs Smb.Routine.PpuFrame

/-- `SavedFInv` with the region named. -/
def AtRegion (rom : UInt16 → UInt8) (g : Global) (Z : Region) (saved : Region → (UInt16 → UInt8) → Prop)
    (r : Region) (s : NES) : Prop :=
  Sch s ∧ s.prg = Smb.prg ∧ ∃ ram0, GInv rom r.prot g ram0 r.T s ∧ saved r ram0 ∧ (r = Z → ZStage s ∨ s.pc = 0x808F)

theorem savedFinv_of_at {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z : Region}
    {saved : Region → (UInt16 → UInt8) → Prop} {r : Region} {s : NES} (hr : r ∈ rs) (h : AtRegion rom g Z saved r s) :
    SavedFInv rom g rs Z saved s := by
  obtain ⟨hS, hP, ram0, hi, hs, hz⟩ := h
  exact ⟨hS, hP, r, hr, ram0, hi, hs, hz⟩

theorem at_of_savedFinv {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z : Region}
    {saved : Region → (UInt16 → UInt8) → Prop} {s : NES} (h : SavedFInv rom g rs Z saved s) :
    ∃ r ∈ rs, AtRegion rom g Z saved r s := by
  obtain ⟨hS, hP, r, hr, ram0, hi, hs, hz⟩ := h
  exact ⟨r, hr, hS, hP, ram0, hi, hs, hz⟩

theorem savedFinv_step_track {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z : Region} {done : UInt16 → Bool}
    {saved : Region → (UInt16 → UInt8) → Prop} {s : NES} {r : Region} (hr : r ∈ rs)
    (hf : SavedFits rom g rs done saved) (hz : ZFits rs Z) (h : AtRegion rom g Z saved r s) (hd : done s.pc = false)
    (hus : s.unmodelled = false) (hu : (CPU.step.run s).2.unmodelled = false)
    (hA : (∀ i : UInt16, (∀ r ∈ rs, r.prot (i &&& 0x7FF) = true) → 0x200 ≤ i &&& 0x7FF → (CPU.step.run s).2.ram.get! (i &&& 0x7FF).toNat = s.ram.get! (i &&& 0x7FF).toNat) → Clean g (CPU.step.run s).2) :
    ∃ r1 ∈ rs, AtRegion rom g Z saved r1 (CPU.step.run s).2 ∧
      (r1 = r ∨ (r.exit s.pc = true ∧ ∃ q ∈ r1.entries, q.pc = s.pc)) ∧
      ∃ ram1, GInv rom r1.prot g ram1 r1.T s ∧ r1.exit s.pc = false ∧ GInv rom r1.prot g ram1 r1.T (CPU.step.run s).2 := by
  obtain ⟨hS, hP, ram0, hi, hsaved, hzs⟩ := h
  have hSS : SchS s := by
    rcases hS with h | h
    · rw [hus] at h; cases h
    · exact h
  have key : ∃ r1 ∈ rs, ∃ ram1, GInv rom r1.prot g ram1 r1.T s ∧ r1.exit s.pc = false ∧ saved r1 ram1 ∧
      (r1 = Z → ZStage s) ∧ (r1 = r ∨ (r.exit s.pc = true ∧ ∃ q ∈ r1.entries, q.pc = s.pc)) := by
    cases hx : r.exit s.pc with
    | false =>
      refine ⟨r, hr, ram0, hi, hx, hsaved, fun e => ?_, Or.inl rfl⟩
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
        refine ⟨r', hr', t.ram, hi', by simpa [hspc] using hx', hsave', fun e => ?_,
          Or.inr ⟨rfl, q, hq, (hqhold.pc.symm.trans hspc.symm)⟩⟩
        have hq8 := hz.entries q (by simpa [e] using hq)
        have hpc : s.pc = 0x8178 := hspc.trans (hqhold.pc.trans hq8)
        rcases hrel with h1 | ⟨h2, _⟩
        · exact ⟨hP, Or.inl ⟨hpc, hSS, h1.ctrl, h1.nmiPending⟩⟩
        · rw [← hspc, hpc] at h2
          exact absurd h2 (by decide)
  obtain ⟨r1, hr1, ram1, hi1, hx1, hsave1, hz1, htr⟩ := key
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
  exact ⟨r1, hr1, ⟨(Pres.step s).1 hS, by rw [(Pres.step s).2]; exact hP, ram1, hnext, hsave1, hstep.2⟩, htr,
    ram1, hi1, hx1, hnext⟩

end Smb.Routine.FrameGuard
