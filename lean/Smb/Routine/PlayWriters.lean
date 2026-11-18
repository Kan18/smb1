import Smb.Routine.PlayCycle
import Smb.Routine.PlayCycleFrames
import Smb.Routine.PlayWritersDefs

/-!
# Which instructions write the VRAM buffer's scheduling cells, in normal play

The buffer's schedule (`Smb.Buffer.Schedule`) assumes its cells have only the writers its automata model: the
buffer-address control `$0773` only `InitBuffer`, the renderers' `SetVRAMCtrl` and `RemoveCoin_Axe`; the parser's
task number `$071F` only its handler; the floatey-number timers `$012C`–`$0131` only `SetupFloateyNumber` and their
countdown; `GameTimerCtrlTimer` (`$0787`) only `ResGTCtrl` and the frame timers' countdown. Three more groups are for
`XInv`'s scroll clause: `FrameCounter` (`$09`) only the handler's `inc`, `Player_Pos_ForScroll` (`$0755`) only
`RenderPlayerSub`'s copy, and `SideCollisionTimer` (`$0785`) only the frame timers' countdown and `ImpedePlayerMove`.

`ginv_step` holds for any exit and protected sets that a table passes `checkF` with. So each region of the normal-play
cycle is checked again on its own table, once per cell group, with the group protected and its writers added to the
exits (`writersOk`). Then a step of normal play changes a group's cells only at its writers (`cycle_step_writers`).
The checks themselves are in `PlayWritersAll`, one module per region, outside the default build.
-/
namespace Smb.Routine.PlayWriters
open Smb NES Smb.Abs Smb.Routine Smb.Routine.FrameGuard Smb.Routine.PlayCycle

/-- A region's invariant, with more cells protected at their present values. -/
theorem ginv_widen {rom : UInt16 → UInt8} {prot : UInt16 → Bool} {g : Global} {ram0 : UInt16 → UInt8} {T : Table}
    {s : NES} (h : GInv rom prot g ram0 T s) (cells : UInt16 → Bool) (hc : ∀ i, cells i = true → i &&& 0x7FF = i) :
    GInv rom (fun i => prot i || cells i) g (fun i => if cells i then s.ram.get! i.toNat else ram0 i) T s := by
  obtain ⟨t, hcode, ⟨b, hbm, hb⟩, hrel⟩ := h
  refine ⟨t, hcode, ⟨b, hbm, { hb with frame := fun i hi => ?_ }⟩, hrel⟩
  cases hci : cells i
  · simp only [hci, Bool.or_false] at hi
    simpa [hci] using hb.frame i hi
  · have e : s.ram.get! (i &&& 0x7FF).toNat = t.ram (i &&& 0x7FF) := by
      rcases hrel with hr | ⟨_, hr⟩
      · exact hr.ram i
      · exact hr.ram i
    rw [hc i hci] at e
    simp [hci, e]

private theorem glob_cyc {s : NES} (h : CycleInv s) (i : UInt16) (hi : i &&& 0x7FF = i) :
    (gAt PlayParser.G i).mem (s.ram.get! i.toNat) = true := by
  obtain ⟨_, _, r, _, ram0, ⟨t, _, ⟨b, _, hb⟩, hr⟩, _, _⟩ := h
  have he : s.ram.get! (i &&& 0x7FF).toNat = t.ram (i &&& 0x7FF) := by
    rcases hr with hr | ⟨_, hr⟩
    · exact hr.ram i
    · exact hr.ram i
  rw [hi] at he
  rw [he]
  exact hb.glob i

private theorem modes_reg {r : Region} (hr : r ∈ regions) : r.prot 0x770 = true ∧ r.prot 0x772 = true := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  exact Bool.and_eq_true_iff.mp (List.all_eq_true.mp modes_protected c hc)

/-- **A step of normal play changes a group's cells only at its writers**, given the regions' checks. -/
theorem cycle_step_writers (hw : ∀ c ∈ configs, writersOk c = true) {k : Group} (hk : k ∈ groups)
    (hc : ∀ i, k.cells i = true → i &&& 0x7FF = i) (hidle : k.writers.contains idlePC = false)
    {s : NES} (h : CycleInv s) (hd : stop s.pc = false) (hus : s.unmodelled = false)
    (hu : (CPU.step.run s).2.unmodelled = false) (hcl : CleanIf (CPU.step.run s).2)
    (hS : k.writers.contains s.pc = false) (i : UInt16) (hi : k.cells i = true) :
    (CPU.step.run s).2.ram.get! i.toNat = s.ram.get! i.toNat := by
  have hstep := savedFinv_step_region (fits checked) (zfits preambles_checked) h hd hus hu (fun hk => by
    apply hcl
    · exact (hk 0x770 (fun r hr => (modes_reg hr).1) (by decide)).trans
        (elems_single mode770 (glob_cyc h 0x770 (by decide)))
    · exact (hk 0x772 (fun r hr => (modes_reg hr).2) (by decide)).trans
        (elems_single mode772 (glob_cyc h 0x772 (by decide))))
  obtain ⟨hg, hnext, r1, hr1, ram1, hi1, hx, _⟩ := hstep
  have hclean : Clean PlayParser.G (CPU.step.run s).2 := by
    apply hcl
    · exact elems_single mode770 (glob_cyc hnext 0x770 (by decide))
    · exact elems_single mode772 (glob_cyc hnext 0x772 (by decide))
  obtain ⟨c1, hc1, rfl⟩ := List.mem_map.mp hr1
  have hok : groupOk c1.exitFn c1.protFn (c1.tableWith PlayParser.G Smb.prg) k = true :=
    List.all_eq_true.mp (hw c1 hc1) k hk
  have hid : c1.exitFn idlePC = false := by
    have := List.all_eq_true.mp idle_go c1 hc1
    simpa using this
  have hx' : c1.exitFn s.pc = false := hx
  have hs := ginv_step hok (by rw [hid, hidle]; rfl) (ginv_widen hi1 k.cells hc)
    (by rw [hx', hS]; rfl) hg hclean
  have := ginv_ram hs i (by simp [hc i hi, hi])
  rw [hc i hi] at this
  simpa [hi] using this

end Smb.Routine.PlayWriters
