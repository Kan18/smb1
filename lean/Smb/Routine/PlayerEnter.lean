import Smb.Routine.PlayKeep
import Smb.Routine.PlayerCtrlLink
import Smb.Routine.BlockPrefix

/-!
# Into the player region, on the full NES

The cycle hands over to the player region at `$8175` (`PlayKeep.Entered`). These facts let the player region's run be
taken on the plain machine from there:

* `plain_step`: the player region's boxes all pass `checkBox` away from its exits and the interrupt's addresses, so
  its first step is the plain machine's, from a plain state in one of its boxes (`enter_ok`), and leaves the NES quiet.
* Its boxes at `$8175` lie in `PlayerPre`'s entry, `PlayerPre`'s at `$B0E9` in `PlayerCtrl`'s, each under bounds
  inside the next region's.
-/
namespace Smb.Routine.PlayerEnter
open Smb NES Smb.Abs Smb.Routine Smb.Routine.FrameGuard Smb.Routine.PlayCycle Smb.Routine.PlayKeep
open Smb.Routine.BlockPrefix

abbrev rom : UInt16 → UInt8 := romOf Smb.prg

/-- A configuration's table passes `checkBox` away from its exits and the interrupt's addresses, and its boxes at
`$8175` lie in `PlayerPre`'s entry. -/
def enterOk (c : Config.C) (prg : ByteArray) : Bool :=
  let T := c.tableWith PlayParser.G prg
  (List.range 0x8000).all (fun n => (T.getD n []).all fun b =>
    c.exitFn b.pc || (checkBox (romOf prg) c.protFn PlayParser.G T b && !onPC b.pc)) &&
  (T.at 0x8175).all (fun b => PlayerPre.conf.entries.any (Box.le PlayParser.G b))

theorem enter_all : configs.all (fun c => !c.entries.all (fun e => e.pc == 0x8175) || enterOk c Smb.prg) = true := by
  native_decide

theorem enter_ok {c : Config.C} (hc : c ∈ configs) (hn : c ∉ restConfigs) : enterOk c Smb.prg = true := by
  have h := List.all_eq_true.mp enter_all c hc
  have hk : c.entries.all (fun e => e.pc == 0x8175) = true := by
    cases hk : c.entries.all (fun e => e.pc == 0x8175) with
    | true => rfl
    | false => exact absurd (List.mem_filter.mpr ⟨hc, by simp [hk]⟩) hn
  simpa [hk] using h

/-- `PlayerPre`'s boxes at `$B0E9` lie in `PlayerCtrl`'s entry; the bounds nest; the routine region's entry has
`S = $F7`, `I` set, and cells below `$0800`; `PlayerPre` has no box at `$AF01`. -/
def preOk (prg : ByteArray) : Bool :=
  ((PlayerPre.conf.table prg).at 0xB0E9).all (fun b => PlayerCtrl.conf.entries.any (Box.le PlayerPre.conf.globals b)) &&
  ((PlayerPre.conf.table prg).at 0xAF01).isEmpty &&
  withinG PlayParser.G PlayerPre.conf.globals && withinG PlayerPre.conf.globals PlayerCtrl.conf.globals &&
  PlayerCtrl.conf.entries.all (fun e => e.s == 0xF7 && e.pc == 0xB0E9 && e.cells.all (fun c => c.1 < 0x800) &&
    (List.range 256).all (fun v => !e.p.mem (UInt8.ofNat v) || (UInt8.ofNat v &&& 4 != 0)))

theorem pre_ok : preOk Smb.prg = true := by native_decide
theorem pre_size : PlayerPre.conf.globals.size = 0x800 := by native_decide
theorem ctrl_size : PlayerCtrl.conf.globals.size = 0x800 := by native_decide

/-- A step that stays in such a configuration's region is the plain machine's, from a state in one of its boxes. -/
theorem plain_step {c : Config.C} (hc : c ∈ configs) (hn : c ∉ restConfigs)
    {s : NES} {ram0 : UInt16 → UInt8} (h : GInv rom c.protFn PlayParser.G ram0 (c.tableWith PlayParser.G Smb.prg) s)
    (hx : c.exitFn s.pc = false) :
    ∃ t c' b, b ∈ (c.tableWith PlayParser.G Smb.prg).at t.regs.pc ∧ Holds c.protFn PlayParser.G ram0 b t ∧
      Code rom t ∧ RelD s t ∧ Rel (CPU.step.run s).2 (CPU.step.run ({ t with cyc := c' } : Plain)).2 := by
  have hp := enter_ok hc hn
  simp only [enterOk, Bool.and_eq_true] at hp
  obtain ⟨t, htc, ⟨b, hbm, hb⟩, hrel⟩ := h
  have hq := List.all_eq_true.mp hp.1 (t.regs.pc &&& 0x7FFF).toNat (List.mem_range.mpr (table_at_lt _))
  have hq2 := List.all_eq_true.mp hq b hbm
  have hspc : s.pc = t.regs.pc := by
    rcases hrel with h1 | ⟨_, h1⟩
    · exact congrArg Regs.pc h1.regs
    · exact congrArg Regs.pc h1.regs
  have hbpc : b.pc = t.regs.pc := hb.pc.symm
  rw [hbpc, ← hspc, hx, Bool.false_or] at hq2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hq2
  obtain ⟨hck, hon⟩ := hq2
  have hrel' : RelD s t := by
    rcases hrel with h1 | ⟨h2, _⟩
    · exact h1
    · rw [← hspc, hon] at h2; cases h2
  obtain ⟨c', hr⟩ := plain_box_rel hrel' htc hb (by rw [hbpc, ← hspc] at *; exact hck)
  exact ⟨t, c', b, hbm, hb, htc, hrel', hr⟩

end Smb.Routine.PlayerEnter
