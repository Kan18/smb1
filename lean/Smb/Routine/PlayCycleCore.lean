import Smb.Routine.PlayCycleMeta
import Smb.Routine.SavedRegions

/-! Normal-play cycle up to explicitly listed open exits. The cycle carries
alternating saved parser/object tuples. It does not establish initial entry,
rule out the open exits, or replace the whole-level timing argument. -/
namespace Smb.Routine.PlayCycle
open Smb Smb.Abs PlaySavedHandoffs

def reg (c : Config.C) : Region :=
  ⟨c.exitFn, c.protFn, c.tableWith PlayParser.G Smb.prg, c.entries⟩
def configs : List Config.C := normalConfigs ++ PlayParser.chunks
def regions : List Region := configs.map reg

def Saved (r : Region) (ram : UInt16 → UInt8) : Prop :=
  (∃ c ∈ normalConfigs, r = reg c ∧ ChainSaved ram) ∨
  (∃ c ∈ PlayParser.chunks, r = reg c ∧ ObjectSaved ram)

theorem normal_cases {c : Config.C} (hc : c ∈ normalConfigs) :
    c = PlayFrame.T ∨ ∃ es, (c, es) ∈ directEdges := by
  simp only [normalConfigs, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr ⟨[(0x8178, PlayFrame.Z), (0x8175, PlayFrame.P)], by simp [directEdges]⟩
  · exact Or.inr ⟨[(0xAF01, PlayEnemy.Front)], by simp [directEdges]⟩
  · exact Or.inr ⟨[(0xAF05, PlayEnemy.E0)], by simp [directEdges]⟩
  · exact Or.inr ⟨[(0xAF0B, PlayEnemy.M0)], by simp [directEdges]⟩
  · exact Or.inr ⟨[(0xAF05, PlayEnemy.E1)], by simp [directEdges]⟩
  · exact Or.inr ⟨[(0xAF0B, PlayEnemy.M1)], by simp [directEdges]⟩
  · exact Or.inr ⟨[(0xAF05, PlayEnemy.E2)], by simp [directEdges]⟩
  · exact Or.inr ⟨[(0xAF0B, PlayEnemy.M2)], by simp [directEdges]⟩
  · exact Or.inr ⟨[(0xAF05, PlayEnemy.E3)], by simp [directEdges]⟩
  · exact Or.inr ⟨[(0xAF0B, PlayEnemy.M3)], by simp [directEdges]⟩
  · exact Or.inr ⟨[(0xAF05, PlayEnemy.E4)], by simp [directEdges]⟩
  · exact Or.inr ⟨[(0xAF0B, PlayEnemy.M4)], by simp [directEdges]⟩
  · exact Or.inr ⟨[(0xAF05, PlayEnemy.E5)], by simp [directEdges]⟩
  · exact Or.inr ⟨[(0xAF0B, PlayEnemy.M5)], by simp [directEdges]⟩
  · exact Or.inr ⟨[(0xAF10, PlayFrame.T)], by simp [directEdges]⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨[(0x808F, PlayFrame.H)], by simp [directEdges]⟩

theorem direct_target {c : Config.C} {es : List (UInt16 × Config.C)}
    (hc : (c, es) ∈ directEdges) {q : UInt16 × Config.C} (hq : q ∈ es) :
    q.2 ∈ normalConfigs := by
  simp only [directEdges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals cases h
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  all_goals first | (rcases hq with rfl | rfl) | cases hq
  all_goals simp [normalConfigs]

/-- Checker results supplied separately from the logical composition. -/
structure Checks : Prop where
  direct : ∀ {c : Config.C} {es : List (UInt16 × Config.C)},
    (c, es) ∈ directEdges →
    c.linked PlayParser.G Smb.prg (es.map (fun (pc, d) => (pc, d.entries))) = true
  parser : PlayParser.chunks.all (PlayParser.accepted Smb.prg) = true

/-- Both table checking and entry membership, without re-running checkers. -/
theorem config_checked (checks : Checks) {c : Config.C} (hc : c ∈ configs) :
    checkF (romOf Smb.prg) c.exitFn c.protFn PlayParser.G (c.tableWith PlayParser.G Smb.prg) = true ∧
    c.entries.all (entryIn PlayParser.G (c.tableWith PlayParser.G Smb.prg)) = true := by
  rcases List.mem_append.mp hc with hn | hp
  · rcases normal_cases hn with rfl | ⟨es, he⟩
    · have h := PlayFrame.acceptedT
      simp only [Smb.Abs.PlayFrame.acceptedT, Bool.and_eq_true] at h
      exact h.1.1.1
    · have h := checks.direct he
      simp only [Config.C.linked, Bool.and_eq_true] at h
      exact h.1
  · have h := List.all_eq_true.mp checks.parser c hp
    simp only [Smb.Abs.PlayParser.accepted, Bool.and_eq_true] at h
    exact h.1.1

private theorem direct_hop (checks : Checks) {c : Config.C} {es : List (UInt16 × Config.C)}
    {ram0 : UInt16 → UInt8} {b : Box} {t : Plain}
    (hn : c ∈ normalConfigs) (hc : (c, es) ∈ directEdges)
    (hb : b ∈ (c.tableWith PlayParser.G Smb.prg).at t.regs.pc)
    (h : Holds c.protFn PlayParser.G ram0 b t) (hs : ChainSaved ram0)
    (hx : c.exitFn t.regs.pc = true) :
    stop t.regs.pc = true ∨ ∃ d ∈ normalConfigs, ∃ e ∈ d.entries,
      d.exitFn t.regs.pc = false ∧ Holds d.protFn PlayParser.G t.ram e t ∧ ChainSaved t.ram := by
  have hw := List.all_eq_true.mp direct_wiring (c, es) hc
  have hm : t.regs.pc ∈ c.exit := by simpa [Config.C.exitFn] using hx
  have hw := List.all_eq_true.mp hw t.regs.pc hm
  rcases Bool.or_eq_true_iff.mp hw with hd | hl
  · exact Or.inl hd
  · obtain ⟨q, hq, hqv⟩ := List.any_eq_true.mp hl
    obtain ⟨heq, hxq⟩ := Bool.and_eq_true_iff.mp hqv
    have heq : t.regs.pc = q.1 := by simpa using heq
    have hxq : q.2.exitFn t.regs.pc = false := by simpa using hxq
    have hc' := checks.direct hc
    simp only [Config.C.linked, Bool.and_eq_true] at hc'
    have hl' := List.all_eq_true.mp hc'.2 (q.1, q.2.entries)
      (List.mem_map.mpr ⟨q, hq, rfl⟩)
    rw [← heq] at hl'
    obtain ⟨e, he, hle⟩ := List.any_eq_true.mp (List.all_eq_true.mp hl' b hb)
    exact Or.inr ⟨q.2, direct_target hc hq, e, he, hxq,
      (h.of_le hle).rebase q.2.protFn, normal_chainSaved_current hn h hs⟩

private theorem reg_mem_normal {c : Config.C} (hc : c ∈ normalConfigs) : reg c ∈ regions :=
  List.mem_map.mpr ⟨c, List.mem_append_left _ hc, rfl⟩

private theorem reg_mem_parser {c : Config.C} (hc : c ∈ PlayParser.chunks) : reg c ∈ regions :=
  List.mem_map.mpr ⟨c, List.mem_append_right _ hc, rfl⟩

/-- Every handoff in the normal cycle is justified, including both saved tuples.
Open exits are deliberate stops, not assumed unreachable. -/
theorem fits (checks : Checks) : SavedFits (romOf Smb.prg) PlayParser.G regions stop Saved := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    exact (config_checked checks hc).1
  · intro r hr
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    have hi := List.all_eq_true.mp idle_go c hc
    simpa [reg] using hi
  · intro r hr
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    exact (config_checked checks hc).2
  · intro r _ ram0 b t hb hh hs hx
    rcases hs with ⟨c, hc, rfl, hs⟩ | ⟨c, hc, rfl, hs⟩
    · rcases normal_cases hc with rfl | ⟨es, he⟩
      · have hm : t.regs.pc ∈ PlayFrame.T.exit := by simpa [reg, Config.C.exitFn] using hx
        rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp tail_wiring t.regs.pc hm) with hd | hp
        · exact Or.inl hd
        · have hp : t.regs.pc = 0xAF67 := by simpa using hp
          obtain ⟨d, hd, e, he, hh', hs'⟩ := tail_to_parser (by simpa [reg, hp] using hb) hh hs
          have hx' := List.all_eq_true.mp parser_go d hd
          refine Or.inr ⟨reg d, reg_mem_parser hd, e, he, ?_, hh', ?_⟩
          · simpa [reg, hp] using hx'
          · exact Or.inr ⟨d, hd, rfl, hs'⟩
      · rcases direct_hop checks hc he hb hh hs hx with hd | ⟨d, hd, e, he, hx', hh', hs'⟩
        · exact Or.inl hd
        · exact Or.inr ⟨reg d, reg_mem_normal hd, e, he, hx', hh', Or.inl ⟨d, hd, rfl, hs'⟩⟩
    · have hm : t.regs.pc ∈ c.exit := by simpa [reg, Config.C.exitFn] using hx
      have hw := List.all_eq_true.mp parser_wiring c hc
      rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp hw t.regs.pc hm) with hd | hp
      · exact Or.inl hd
      · have hp : t.regs.pc = 0x8178 := by simpa using hp
        obtain ⟨e, he, hh', hs'⟩ := parser_to_closing hc
          (List.all_eq_true.mp checks.parser c hc) (by simpa [reg, hp] using hb) hh hs
        have hz : PlayFrame.Z ∈ normalConfigs := by simp [normalConfigs]
        refine Or.inr ⟨reg PlayFrame.Z, reg_mem_normal hz, e, he, ?_, hh', ?_⟩
        · simpa [reg, hp] using closing_go
        · exact Or.inl ⟨PlayFrame.Z, hz, rfl, hs'⟩

/-- Conditional closure for arbitrary instruction counts and controller inputs. -/
theorem invariant (checks : Checks) {n : Nat} {s : NES}
    (hd : ∀ i, i < n → stop (stepN i s).pc = false)
    (hg : ∀ i, i < n → Guard (stepN i s))
    (hA : ∀ i, i < n → Clean PlayParser.G (stepN (i + 1) s))
    (h : SavedInv (romOf Smb.prg) PlayParser.G regions Saved s) :
    SavedInv (romOf Smb.prg) PlayParser.G regions Saved (stepN n s) :=
  savedInv_stepN (fits checks) n s hd hg hA h

end Smb.Routine.PlayCycle
