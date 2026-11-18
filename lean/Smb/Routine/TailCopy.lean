import Smb.Routine.TimerKeep
import Smb.Routine.FrameGuard

/-!
# `PlayerGfxHandler`'s copy of the on-screen X

`GameEngine` calls `PlayerGfxHandler` at `$AF16`, right after `RelativePlayerPosition` has set `$03AD` to `$86 − $071C`
(`RelativePosition.relPlayerCall`). Every path through it reaches `RenderPlayerSub`, whose `lda $03AD` / `sta $0755`
(`$EFC0`/`$EFC3`) copies that into `Player_Pos_ForScroll`, except the blink (`InjuryTimer` `$079E` nonzero on an odd
frame). `XInv`'s scroll clause needs only: with no injury, `$03AD` below `$50` leaves `$0755` below `$50`.

A variant of the tail's table shows it. Its entries are `T`'s own boxes at `$AF16`, split by `$03AD`'s band (below
`$50` or not) and `$079E`'s (zero, `$01`–`$80`, `$81`–`$FF`: a tracked set over 240 values counts as unknown), kept apart by `splitcb`; `$03AD` is protected, `$0755`, `$03AD` and
`$079E` tracked, and `$AF19` (the return) is an exit. `copyOk` checks the table, its entries, that no box reaches
`$AF67` (the tail's normal exit) first, and the band property at `$AF19`.
-/
namespace Smb.Routine.TailCopy
open Smb Smb.Abs Smb.Abs.Config Smb.Routine.PlayCycle Smb.Routine.TimerKeep

def tbC : Config.C := { PlayFrame.T with
  exit := 0xAF19 :: PlayFrame.T.exit,
  prot := (0x3AD, 0x3AD) :: PlayFrame.T.prot,
  track := (0x755, 0x755) :: (0x3AD, 0x3AD) :: (0x79E, 0x79E) :: PlayFrame.T.track,
  splitCellBands := (0x3AD, 0x8000, 0xFFFF, [0x50]) :: (0x79E, 0x8000, 0xFFFF, [1, 0x81]) :: PlayFrame.T.splitCellBands }

def bands : List (VS × VS) :=
  [rng 0 0x4F, rng 0x50 0xFF].flatMap fun r3 => [rng 0 0, rng 1 0x80, rng 0x81 0xFF].map fun r7 => (r3, r7)

def tbEntries : List Box := ((reg PlayFrame.T).T.at 0xAF16).flatMap fun b =>
  bands.map fun (r3, r7) => { b with cells := Cells.set (Cells.set b.cells 0x3AD r3) 0x79E r7 }

def tbTable : Table := (fixpoint (tbC.cfg (romOf Smb.prg) PlayParser.G tbC.track) tbEntries).table

def low (v : VS) : Bool := v.elems.all (· < 0x50)

/-- At `$AF19`: `$079E` can't be zero, or `$03AD` is at least `$50`, or `$03AD` and `$0755` are both below `$50`. -/
def bandOk (b : Box) : Bool :=
  b.pc != 0xAF19 ||
    (match cellVS b.cells 0x79E with | some r7 => !r7.mem 0 | none => false) ||
    match cellVS b.cells 0x3AD with
    | some r3 => r3.elems.all (0x50 ≤ ·) || (low r3 && match cellVS b.cells 0x755 with | some r5 => low r5 | none => false)
    | none => false

def copyOk : Bool :=
  let T := tbTable
  checkF (romOf Smb.prg) tbC.exitFn tbC.protFn PlayParser.G T && tbEntries.all (entryIn PlayParser.G T) &&
    (T.at 0xAF67).isEmpty && (List.range 0x8000).all fun n => (T.getD n []).all bandOk

theorem copy_ok : copyOk = true := by native_decide

private theorem inR_cons {u v : Nat} {l : List (Nat × Nat)} {a : UInt16} :
    inR ((u, v) :: l) a = ((u ≤ a.toNat && a.toNat ≤ v) || inR l a) := by
  simp [inR, List.any_cons]

/-- **From `$AF16` to the first exit**: not the tail's normal exit; at `$AF19`, with no injury and `$03AD` below
`$50`, `$0755` is below `$50`; and `$03AD` as it was. -/
theorem copy_run {s : NES} {ram0 : UInt16 → UInt8}
    (h : GInv (romOf Smb.prg) (reg PlayFrame.T).prot PlayParser.G ram0 (reg PlayFrame.T).T s) (hpc : s.pc = 0xAF16)
    (n : Nat) (hx : ∀ i, i < n → tbC.exitFn (stepN i s).pc = false) (hg : ∀ i, i < n → Guard (stepN i s))
    (hA : ∀ i, i < n → Clean PlayParser.G (stepN (i + 1) s)) (hend : tbC.exitFn (stepN n s).pc = true) :
    (stepN n s).pc ≠ 0xAF67 ∧
    ((stepN n s).pc = 0xAF19 → (stepN n s).ram.get! 0x79E = 0 → ((stepN n s).ram.get! 0x3AD).toNat < 0x50 →
      ((stepN n s).ram.get! 0x755).toNat < 0x50) ∧
    (stepN n s).ram.get! 0x3AD = s.ram.get! 0x3AD := by
  obtain ⟨t, hcode, ⟨b, hbm, hb⟩, hrel⟩ := h
  have hram : ∀ i : UInt16, i &&& 0x7FF = i → s.ram.get! i.toNat = t.ram i := by
    intro i hi
    have e : s.ram.get! (i &&& 0x7FF).toNat = t.ram (i &&& 0x7FF) := by
      rcases hrel with hr | ⟨_, hr⟩
      · exact hr.ram i
      · exact hr.ram i
    rwa [hi] at e
  have htpc : t.regs.pc = 0xAF16 := by
    rcases hrel with hr | ⟨_, hr⟩
    · exact (congrArg Regs.pc hr.regs).symm.trans hpc
    · exact (congrArg Regs.pc hr.regs).symm.trans hpc
  have hok := copy_ok
  simp only [copyOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨⟨hchk, hent⟩, h67⟩, hband⟩ := hok
  -- The band the state is in.
  let v3 := t.ram 0x3AD
  let v7 := t.ram 0x79E
  have hpick : ∃ p ∈ bands, p.1.mem v3 = true ∧ p.2.mem v7 = true := by
    have h3 := v3.toNat_lt
    have h7 := v7.toNat_lt
    by_cases a3 : v3.toNat ≤ 0x4F
    · by_cases a7 : v7.toNat = 0
      · exact ⟨(rng 0 0x4F, rng 0 0), by simp [bands], mem_rng (by omega) a3 (by decide), mem_rng (by omega) (by omega) (by decide)⟩
      · by_cases b7 : v7.toNat ≤ 0x80
        · exact ⟨(rng 0 0x4F, rng 1 0x80), by simp [bands], mem_rng (by omega) a3 (by decide), mem_rng (by omega) b7 (by decide)⟩
        · exact ⟨(rng 0 0x4F, rng 0x81 0xFF), by simp [bands], mem_rng (by omega) a3 (by decide), mem_rng (by omega) (by omega) (by decide)⟩
    · by_cases a7 : v7.toNat = 0
      · exact ⟨(rng 0x50 0xFF, rng 0 0), by simp [bands], mem_rng (by omega) (by omega) (by decide), mem_rng (by omega) (by omega) (by decide)⟩
      · by_cases b7 : v7.toNat ≤ 0x80
        · exact ⟨(rng 0x50 0xFF, rng 1 0x80), by simp [bands], mem_rng (by omega) (by omega) (by decide), mem_rng (by omega) b7 (by decide)⟩
        · exact ⟨(rng 0x50 0xFF, rng 0x81 0xFF), by simp [bands], mem_rng (by omega) (by omega) (by decide), mem_rng (by omega) (by omega) (by decide)⟩
  obtain ⟨⟨r3, r7⟩, hp, hm3, hm7⟩ := hpick
  let e : Box := { b with cells := Cells.set (Cells.set b.cells 0x3AD r3) 0x79E r7 }
  have he : e ∈ tbEntries := List.mem_flatMap.mpr ⟨b, by rw [← htpc]; exact hbm, List.mem_map.mpr ⟨(r3, r7), hp, rfl⟩⟩
  let ram0' : UInt16 → UInt8 := fun i => if i = 0x3AD then t.ram 0x3AD else ram0 i
  have hcells : ∀ c ∈ e.cells, c.2.mem (t.ram c.1) = true := by
    intro c hc
    rcases mem_cells_set hc with rfl | hc
    · exact hm7
    · rcases mem_cells_set hc with rfl | hc
      · exact hm3
      · exact hb.cells c hc
  have hframe : ∀ i, tbC.protFn i = true → t.ram i = ram0' i := by
    intro i hi
    simp only [tbC, Config.C.protFn, inR_cons, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hi
    by_cases e3 : i = 0x3AD
    · simp [ram0', e3]
    · simp only [ram0', e3, if_false]
      rcases hi with ⟨h1, h2⟩ | hi
      · exact absurd (UInt16.toNat_inj.mp (by simp; omega)) e3
      · exact hb.frame i hi
  have hhe : Holds tbC.protFn PlayParser.G ram0' e t := { hb with cells := hcells, frame := hframe }
  have hidle : tbC.exitFn idlePC = false := by
    have := List.all_eq_true.mp idle_go PlayFrame.T (by simp [PlaySavedHandoffs.normalConfigs])
    simp only [tbC, Config.C.exitFn, List.contains_cons]
    simp only [Config.C.exitFn] at this
    simpa [idlePC] using this
  have hg0 : GInv (romOf Smb.prg) tbC.protFn PlayParser.G ram0' tbTable s := ⟨t, hcode, inv_of_entry (hent e he) hhe, hrel⟩
  have hgn := ginv_stepN hchk hidle n s hx hg hA hg0
  have hkeep : (stepN n s).ram.get! 0x3AD = s.ram.get! 0x3AD := by
    have := Smb.Routine.FrameGuard.ginv_ram hgn 0x3AD (by simp [tbC, Config.C.protFn, inR_cons])
    rw [show (0x3AD : UInt16) &&& 0x7FF = 0x3AD by decide] at this
    have e0 := hram 0x3AD (by decide)
    simp only [UInt16.reduceToNat] at this e0 ⊢
    rw [this, e0]
    simp [ram0']
  obtain ⟨t', _, ⟨b', hbm', hb'⟩, hrel'⟩ := hgn
  have hram' : ∀ i : UInt16, i &&& 0x7FF = i → (stepN n s).ram.get! i.toNat = t'.ram i := by
    intro i hi
    have e : (stepN n s).ram.get! (i &&& 0x7FF).toNat = t'.ram (i &&& 0x7FF) := by
      rcases hrel' with hr | ⟨_, hr⟩
      · exact hr.ram i
      · exact hr.ram i
    rwa [hi] at e
  have hpc' : b'.pc = (stepN n s).pc := by
    rcases hrel' with hr | ⟨_, hr⟩
    · exact hb'.pc.symm.trans (congrArg Regs.pc hr.regs).symm
    · exact hb'.pc.symm.trans (congrArg Regs.pc hr.regs).symm
  rw [hb'.pc, hpc'] at hbm'
  refine ⟨fun e67 => ?_, fun e19 h7 h3 => ?_, hkeep⟩
  · rw [e67] at hbm'
    rw [List.isEmpty_iff.mp h67] at hbm'
    cases hbm'
  · have hbo := hband _ (List.mem_range.mpr (table_at_lt (stepN n s).pc)) b' (by simpa [Table.at] using hbm')
    simp only [bandOk, hpc', e19, bne_self_eq_false, Bool.false_or, Bool.or_eq_true] at hbo
    have e7 := hram' 0x79E (by decide)
    have e3 := hram' 0x3AD (by decide)
    have e5 := hram' 0x755 (by decide)
    simp only [UInt16.reduceToNat] at e7 e3 e5 h7 h3 ⊢
    rw [e7] at h7
    rw [e3] at h3
    rw [e5]
    rcases hbo with h7' | h3'
    · cases hv : cellVS b'.cells 0x79E with
      | none => rw [hv] at h7'; cases h7'
      | some r =>
        rw [hv] at h7'
        have := hb'.cells _ (cellVS_sound hv)
        simp only at this
        rw [h7] at this
        simp [this] at h7'
    · cases hv3 : cellVS b'.cells 0x3AD with
      | none => rw [hv3] at h3'; cases h3'
      | some r3' =>
        rw [hv3] at h3'
        have hm := hb'.cells _ (cellVS_sound hv3)
        simp only at hm
        simp only [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true] at h3'
        rcases h3' with hall | ⟨_, h5⟩
        · have := hall _ (VS.mem_elems hm)
          have : 0x50 ≤ (t'.ram 0x3AD).toNat := UInt8.le_iff_toNat_le.mp (of_decide_eq_true this)
          omega
        · cases hv5 : cellVS b'.cells 0x755 with
          | none => rw [hv5] at h5; cases h5
          | some r5 =>
            rw [hv5] at h5
            have hm5 := hb'.cells _ (cellVS_sound hv5)
            simp only at hm5
            simp only [low, List.all_eq_true] at h5
            exact UInt8.lt_iff_toNat_lt.mp (of_decide_eq_true (h5 _ (VS.mem_elems hm5)))

end Smb.Routine.TailCopy
