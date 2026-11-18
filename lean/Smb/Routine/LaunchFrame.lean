import Smb.Routine.FrameGuard
import Smb.Routine.LaunchPhaseH
import Smb.Routine.LaunchPhaseQ
import Smb.Routine.LaunchPhaseR
import Smb.Routine.LaunchPhaseE
import Smb.Routine.LaunchPhaseT
import Smb.Routine.LaunchPhaseA
import Smb.Routine.LaunchPhaseB
import Smb.Routine.LaunchPhaseZ

/-!
# A launch frame's regions, composed

Eight regions cover a frame during the launch, all but `PlayerCtrlRoutine`. A frame goes through three runs of them, each closed under `FrameGuard`, so in each run every state stays in a table, the shared bounds hold, and the cells those regions protect keep their values:

* `rsP`, from the idle loop through the next NMI to the routine's entry
* `rsM`, from the routine's end to `$AF67`
* `rsT`, from `$AF6B` through the handler's end to the idle loop

`SaveAB`, at `$AF67`, sits between the last two, in `A`. It's the only region here that changes `$0D`.
-/
namespace Smb.Routine.LaunchPhase
open Smb NES Smb.Abs Smb.Abs.LaunchPhase Smb.Routine.FrameGuard

def reg (c : Config.C) : Region := ⟨c.exitFn, c.protFn, c.tableWith G Smb.prg, c.entries⟩

def regions : List Region := [reg H, reg Q, reg R, reg E, reg T, reg A, reg B, reg Z]

/-- Where a run stops: the routine's entry, the timer running out, or where normal control ends. -/
def stop (pc : UInt16) : Bool := pc == 0xB0E9 || pc == 0xB79A || doneList.contains pc

def Parts (c : Config.C) (nexts : List (UInt16 × List Box)) (empties : List UInt16) : Prop :=
    checkF (romOf Smb.prg) c.exitFn c.protFn G (c.tableWith G Smb.prg) = true ∧
    c.entries.all (entryIn G (c.tableWith G Smb.prg)) = true ∧
    (∀ q ∈ nexts, ((c.tableWith G Smb.prg).at q.1).all (fun b => q.2.any (Box.le G b)) = true) ∧
    ∀ pc ∈ empties, (c.tableWith G Smb.prg).at pc = []

theorem parts {c : Config.C} {nexts : List (UInt16 × List Box)} {empties : List UInt16} (h : c.linkedE G Smb.prg nexts empties = true) : Parts c nexts empties := by
  simp only [Config.C.linkedE, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, List.all_eq_true.mpr h2, fun q hq => List.all_eq_true.mpr (h3 q hq), h4⟩

theorem pH : Parts H [(0x8175, Q.entries), (0x8178, Z.entries)] (preList ++ idleList ++ doneList ++ timeList ++ entryList) := parts linkedH
theorem pQ : Parts Q [] (preList ++ idleList ++ doneList ++ timeList) := parts linkedQ
theorem pR : Parts R [(0xAF01, E.entries)] (preList ++ idleList ++ doneList ++ timeList ++ entryList ++ saveList) := parts linkedR
theorem pE : Parts E [(0xAF10, T.entries)] (preList ++ idleList ++ doneList ++ timeList ++ entryList ++ saveList) := parts linkedE
theorem pT : Parts T [(0xAF67, A.entries)] (preList ++ idleList ++ doneList ++ entryList) := parts linkedT
theorem pA : Parts A [(0xAF6B, B.entries)] (preList ++ idleList ++ doneList ++ timeList ++ entryList) := parts linkedA
theorem pB : Parts B [(0x8178, Z.entries)] (preList ++ idleList ++ doneList ++ timeList ++ entryList) := parts linkedB
theorem pZ : Parts Z [(0x808F, H.entries)] (doneList ++ timeList ++ entryList) := parts linkedZ

theorem exH : H.exit.all (fun pc => stop pc || pc == 0x8175 || pc == 0x8178) = true := by native_decide
theorem idleH : H.exitFn idlePC = false := by native_decide
theorem exQ : Q.exit.all (fun pc => stop pc) = true := by native_decide
theorem idleQ : Q.exitFn idlePC = false := by native_decide
theorem exR : R.exit.all (fun pc => stop pc || pc == 0xAF01) = true := by native_decide
theorem idleR : R.exitFn idlePC = false := by native_decide
theorem exE : E.exit.all (fun pc => stop pc || pc == 0xAF10) = true := by native_decide
theorem idleE : E.exitFn idlePC = false := by native_decide
theorem exT : T.exit.all (fun pc => stop pc || pc == 0xAF67) = true := by native_decide
theorem idleT : T.exitFn idlePC = false := by native_decide
theorem exA : A.exit.all (fun pc => stop pc || pc == 0xAF6B) = true := by native_decide
theorem idleA : A.exitFn idlePC = false := by native_decide
theorem exB : B.exit.all (fun pc => stop pc || pc == 0x8178) = true := by native_decide
theorem idleB : B.exitFn idlePC = false := by native_decide
theorem exZ : Z.exit.all (fun pc => stop pc || pc == 0x808F) = true := by native_decide
theorem idleZ : Z.exitFn idlePC = false := by native_decide

theorem entZ : Z.entries.all (fun e => e.pc == 0x8178) = true := by native_decide
theorem x808F : Z.exitFn 0x808F = true := by native_decide
theorem go8175 : Q.exitFn 0x8175 = false := by native_decide
theorem go8178 : Z.exitFn 0x8178 = false := by native_decide
theorem goAF01 : E.exitFn 0xAF01 = false := by native_decide
theorem goAF10 : T.exitFn 0xAF10 = false := by native_decide
theorem goAF67 : A.exitFn 0xAF67 = false := by native_decide
theorem goAF6B : B.exitFn 0xAF6B = false := by native_decide
theorem go808F : H.exitFn 0x808F = false := by native_decide

theorem exit_mem {c : Config.C} {pc : UInt16} (h : c.exitFn pc = true) : pc ∈ c.exit := by
  simpa [Config.C.exitFn] using h

theorem reg_chk (r : Region) (hr : r ∈ regions) : checkF (romOf Smb.prg) r.exit r.prot G r.T = true := by
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pH.1
    · exact pQ.1
    · exact pR.1
    · exact pE.1
    · exact pT.1
    · exact pA.1
    · exact pB.1
    · exact pZ.1

theorem reg_idle (r : Region) (hr : r ∈ regions) : r.exit idlePC = false := by
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact idleH
    · exact idleQ
    · exact idleR
    · exact idleE
    · exact idleT
    · exact idleA
    · exact idleB
    · exact idleZ

theorem reg_entries (r : Region) (hr : r ∈ regions) : r.entries.all (entryIn G r.T) = true := by
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pH.2.1
    · exact pQ.2.1
    · exact pR.2.1
    · exact pE.2.1
    · exact pT.2.1
    · exact pA.2.1
    · exact pB.2.1
    · exact pZ.2.1

/-- From the idle loop to the routine's entry. -/
def rsP : List Region := [reg H, reg Q, reg Z]

def stopP (pc : UInt16) : Bool := stop pc

theorem rsP_sub (r : Region) (hr : r ∈ rsP) : r ∈ regions := by
  simp only [rsP, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp [regions]

theorem fits_rsP : Fits (romOf Smb.prg) G rsP stopP := by
  refine ⟨fun r hr => reg_chk r (rsP_sub r hr), fun r hr => reg_idle r (rsP_sub r hr), fun r hr => reg_entries r (rsP_sub r hr), ?_⟩
  · intro r hr pc hx
    simp only [rsP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have h := List.all_eq_true.mp exH pc (exit_mem hx)
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with (h | rfl) | rfl
      · exact Or.inl (by simp [stopP, h])
      · exact Or.inr ⟨reg Q, by simp [rsP], go8175, pH.2.2.1 (0x8175, Q.entries) (by simp)⟩
      · exact Or.inr ⟨reg Z, by simp [rsP], go8178, pH.2.2.1 (0x8178, Z.entries) (by simp)⟩
    · have h := List.all_eq_true.mp exQ pc (exit_mem hx)
      exact Or.inl (by simp [stopP, h])
    · have h := List.all_eq_true.mp exZ pc (exit_mem hx)
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | rfl
      · exact Or.inl (by simp [stopP, h])
      · exact Or.inr ⟨reg H, by simp [rsP], go808F, pZ.2.2.1 (0x808F, H.entries) (by simp)⟩

/-- From the routine's end to `SaveAB`. -/
def rsM : List Region := [reg R, reg E, reg T]

def stopM (pc : UInt16) : Bool := stop pc || pc == 0xAF67

theorem rsM_sub (r : Region) (hr : r ∈ rsM) : r ∈ regions := by
  simp only [rsM, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp [regions]

theorem fits_rsM : Fits (romOf Smb.prg) G rsM stopM := by
  refine ⟨fun r hr => reg_chk r (rsM_sub r hr), fun r hr => reg_idle r (rsM_sub r hr), fun r hr => reg_entries r (rsM_sub r hr), ?_⟩
  · intro r hr pc hx
    simp only [rsM, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have h := List.all_eq_true.mp exR pc (exit_mem hx)
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | rfl
      · exact Or.inl (by simp [stopM, h])
      · exact Or.inr ⟨reg E, by simp [rsM], goAF01, pR.2.2.1 (0xAF01, E.entries) (by simp)⟩
    · have h := List.all_eq_true.mp exE pc (exit_mem hx)
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | rfl
      · exact Or.inl (by simp [stopM, h])
      · exact Or.inr ⟨reg T, by simp [rsM], goAF10, pE.2.2.1 (0xAF10, T.entries) (by simp)⟩
    · have h := List.all_eq_true.mp exT pc (exit_mem hx)
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | rfl
      · exact Or.inl (by simp [stopM, h])
      · exact Or.inl (by simp [stopM])

/-- From `SaveAB`'s end to the next NMI. -/
def rsT : List Region := [reg B, reg Z]

def stopT (pc : UInt16) : Bool := stop pc || pc == 0x808F

theorem rsT_sub (r : Region) (hr : r ∈ rsT) : r ∈ regions := by
  simp only [rsT, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp [regions]

theorem fits_rsT : Fits (romOf Smb.prg) G rsT stopT := by
  refine ⟨fun r hr => reg_chk r (rsT_sub r hr), fun r hr => reg_idle r (rsT_sub r hr), fun r hr => reg_entries r (rsT_sub r hr), ?_⟩
  · intro r hr pc hx
    simp only [rsT, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have h := List.all_eq_true.mp exB pc (exit_mem hx)
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | rfl
      · exact Or.inl (by simp [stopT, h])
      · exact Or.inr ⟨reg Z, by simp [rsT], go8178, pB.2.2.1 (0x8178, Z.entries) (by simp)⟩
    · have h := List.all_eq_true.mp exZ pc (exit_mem hx)
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | rfl
      · exact Or.inl (by simp [stopT, h])
      · exact Or.inl (by simp [stopT])


theorem zfits_all : ZFits regions (reg Z) := by
  refine ⟨fun e he => ?_, x808F, ?_⟩
  · have h := List.all_eq_true.mp entZ e he
    simpa using h
  · intro r hr hne pc hp
    have hp' : pc ∈ preList := by
      simp only [preamblePC, onExit, Bool.or_eq_true, beq_iff_eq] at hp
      simp only [preList, List.mem_cons, List.not_mem_nil, or_false]
      rcases hp with (((h | h) | h) | h) | h <;> simp [h]
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pH.2.2.2 pc (by simp [List.mem_append, hp'])
    · exact pQ.2.2.2 pc (by simp [List.mem_append, hp'])
    · exact pR.2.2.2 pc (by simp [List.mem_append, hp'])
    · exact pE.2.2.2 pc (by simp [List.mem_append, hp'])
    · exact pT.2.2.2 pc (by simp [List.mem_append, hp'])
    · exact pA.2.2.2 pc (by simp [List.mem_append, hp'])
    · exact pB.2.2.2 pc (by simp [List.mem_append, hp'])
    · exact absurd rfl hne

theorem zfits_of {rs : List Region} (hs : ∀ r ∈ rs, r ∈ regions) : ZFits rs (reg Z) :=
  ⟨zfits_all.entries, zfits_all.exit, fun r hr => zfits_all.empty r (hs r hr)⟩

end Smb.Routine.LaunchPhase
