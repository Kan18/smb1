import Smb.Abs.FrameData
import Smb.Routine.FrameGuard
import Smb.Routine.FrameH
import Smb.Routine.FrameZ
import Smb.Routine.HorizontalLimit

/-!
# Frames that don't reach the game logic, without `Guard`

Two of a frame's regions, on the ROM: the NMI handler up to the game logic, and the handler's end through the idle loop and the next NMI up to `$808F`. Together they're a closed invariant
over instruction steps, stopping when `$8175` calls the game logic or a store that ends normal control comes up.

No hypothesis about NMI timing or lag: `Guard` is a conclusion here. What's assumed of the start: it's at the handler's entry, in an entry box, with a well-formed PPU schedule. What's
assumed of the run: it never sets `unmodelled`.

The other regions, which the game logic runs in, aren't in this theorem.
-/
namespace Smb.Routine.Frame
open Smb NES Smb.Abs Smb.Abs.Frame Smb.Routine.FrameGuard

def reg (c : Config.C) : Region := ⟨c.exitFn, c.protFn, c.tableWith G Smb.prg, c.entries⟩

def regions : List Region := [reg H, reg Z]

/-- The run stops at the game logic's call, or at a store that ends normal control. -/
def stop (pc : UInt16) : Bool := done pc || pc == 0x8175

/-- What a region's check gives. -/
def Parts (c : Config.C) (nexts : List (UInt16 × List Box)) (empties : List UInt16) : Prop :=
    checkF (romOf Smb.prg) c.exitFn c.protFn G (c.tableWith G Smb.prg) = true ∧
    c.entries.all (entryIn G (c.tableWith G Smb.prg)) = true ∧
    (∀ q ∈ nexts, ((c.tableWith G Smb.prg).at q.1).all (fun b => q.2.any (Box.le G b)) = true) ∧
    ∀ pc ∈ empties, (c.tableWith G Smb.prg).at pc = []

theorem parts {c : Config.C} {nexts : List (UInt16 × List Box)} {empties : List UInt16} (h : c.linkedE G Smb.prg nexts empties = true) : Parts c nexts empties := by
  simp only [Config.C.linkedE, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, List.all_eq_true.mpr h2, fun q hq => List.all_eq_true.mpr (h3 q hq), h4⟩

theorem pH : Parts H [(0x8178, Z.entries)] [0x8082, 0x8085, 0x8087, 0x808A, 0x808C] := parts linkedH
theorem pZ : Parts Z [(0x808F, H.entries)] [] := parts linkedZ

theorem exH : H.exit.all (fun pc => stop pc || pc == 0x8178) = true := by native_decide
theorem exZ : Z.exit.all (fun pc => stop pc || pc == 0x808F) = true := by native_decide
theorem entZ : Z.entries.all (fun e => e.pc == 0x8178) = true := by native_decide

theorem idleH : H.exitFn idlePC = false := by native_decide
theorem idleZ : Z.exitFn idlePC = false := by native_decide
theorem go8178 : Z.exitFn 0x8178 = false := by native_decide
theorem go808F : H.exitFn 0x808F = false := by native_decide
theorem x808F : Z.exitFn 0x808F = true := by native_decide
theorem xH : H.exitFn 0x8175 = true := by native_decide
theorem xZ : Z.exitFn 0x8175 = false := by native_decide

theorem exit_mem {c : Config.C} {pc : UInt16} (h : c.exitFn pc = true) : pc ∈ c.exit := by
  simpa [Config.C.exitFn] using h

theorem fits : Fits (romOf Smb.prg) G regions stop := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pH.1
    · exact pZ.1
  · intro r hr
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact idleH
    · exact idleZ
  · intro r hr
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pH.2.1
    · exact pZ.2.1
  · intro r hr pc hx
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have h := List.all_eq_true.mp exH pc (exit_mem hx)
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨reg Z, by simp [regions], go8178, pH.2.2.1 (0x8178, Z.entries) (by simp)⟩
    · have h := List.all_eq_true.mp exZ pc (exit_mem hx)
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨reg H, by simp [regions], go808F, pZ.2.2.1 (0x808F, H.entries) (by simp)⟩

theorem reg_ne : reg H ≠ reg Z := by
  intro e
  have e1 : H.exitFn = Z.exitFn := congrArg Region.exit e
  have e2 := congrFun e1 0x8175
  rw [xH, xZ] at e2
  cases e2

theorem zfits : ZFits regions (reg Z) := by
  refine ⟨fun e he => ?_, x808F, ?_⟩
  · have h := List.all_eq_true.mp entZ e he
    simpa using h
  · intro r hr hne pc hp
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine pH.2.2.2 pc ?_
      simp only [preamblePC, onExit, Bool.or_eq_true, beq_iff_eq] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hp with (((h | h) | h) | h) | h <;> simp [h]
    · exact absurd rfl hne

theorem code_toPlain (s : NES) (hprg : s.prg = Smb.prg) : Code (romOf Smb.prg) s.toPlain := by
  intro a _
  show s.prg.get! ((a &&& 0x7FFF) &&& 0x7FFF).toNat = Smb.prg.get! (a &&& 0x7FFF).toNat
  rw [hprg, and_idem]

/-- These two regions don't bound the assumed cells, so a run needs no clean hypothesis here. -/
theorem G_topB : topB (gAt G 0x300) = true := by native_decide
theorem G_top : gAt G 0x300 = .top := eq_top_of_topB G_topB
theorem G_topB2 : topB (gAt G 0x340) = true := by native_decide
theorem G_top2 : gAt G 0x340 = .top := eq_top_of_topB G_topB2

/-- A state at the handler's entry, in one of its entry boxes, with a well-formed PPU schedule. -/
def Start (s : NES) : Prop :=
  s.prg = Smb.prg ∧ s.Quiet ∧ Sch s ∧ ∃ e ∈ H.entries, Holds H.protFn G s.toPlain.ram e s.toPlain

theorem start_inv {s : NES} (h : Start s) : FInv (romOf Smb.prg) G regions (reg Z) s := by
  obtain ⟨hprg, hq, hs, e, he, hh⟩ := h
  refine FInv.of_start hs hprg (r := reg H) (by simp [regions]) reg_ne (ram0 := s.toPlain.ram) ⟨s.toPlain, code_toPlain s hprg, ?_, Or.inl (RelD.of_rel (NES.rel_toPlain s hq))⟩
  exact inv_of_entry (List.all_eq_true.mp pH.2.1 e he) hh

/-- Invariance under CPU instruction iteration, conditional on no stop and supportedness.
This does not yet transport changing per-frame inputs through `NES.frame` / `runFrames`. -/
theorem invariant (s : NES) (n : Nat) (h : Start s)
    (hd : ∀ i, i < n → stop (stepN i s).pc = false) (hu : ∀ i, i ≤ n → (stepN i s).unmodelled = false) :
    FInv (romOf Smb.prg) G regions (reg Z) (stepN n s) :=
  finv_stepN fits zfits n s hd hu (fun _ _ => clean_of_top G_top G_top2 _) (start_inv h)

/-- `Guard` holds at every step: no NMI arrives during the handler's first instructions, and `sta $2000` there takes effect. -/
theorem no_guard (s : NES) (n : Nat) (h : Start s)
    (hd : ∀ i, i ≤ n → stop (stepN i s).pc = false) (hu : ∀ i, i ≤ n + 1 → (stepN i s).unmodelled = false) :
    Guard (stepN n s) :=
  finv_guard fits zfits n s hd hu (fun _ _ => clean_of_top G_top G_top2 _) (start_inv h)

/-- RAM stays within the shared bounds. -/
theorem bounds (s : NES) (n : Nat) (h : Start s)
    (hd : ∀ i, i < n → stop (stepN i s).pc = false) (hu : ∀ i, i ≤ n → (stepN i s).unmodelled = false) (i : UInt16) (hi : i < 0x800) :
    (gAt G i).mem ((stepN n s).ram.get! i.toNat) = true := by
  obtain ⟨r, _, ram0, t, _, ⟨b, _, hb⟩, hr⟩ := (invariant s n h hd hu).rinv
  have hm : i &&& 0x7FF = i := by revert hi; bv_decide (config := { enums := false })
  have h2 : (stepN n s).ram.get! (i &&& 0x7FF).toNat = t.ram (i &&& 0x7FF) := by
    rcases hr with hr | ⟨_, hr⟩
    · exact hr.ram i
    · exact hr.ram i
  rw [hm] at h2
  rw [h2]
  exact hb.glob i

end Smb.Routine.Frame
