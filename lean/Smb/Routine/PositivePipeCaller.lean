import Smb.Routine.LandPlyr
import Smb.Routine.Landing
import Smb.Routine.WarpDestination

/-!
Positive local caller fragment. It starts after the foot collision has
selected LandPlyr with left tile $10 and stops at the JSR target $DEE8,
the entry used by WarpDestination.handlePipeEntry_rom.
-/

namespace Smb.Routine.PositivePipeCaller
open Smb.Routine

def PipeCallerSummary (ram prg : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xDEE8 ∧ t.bad = false ∧
  t.prg = prg ∧ (t.regs.p &&& 4 == 0) = false ∧
  t.ram 0 = ram 0 ∧ t.ram 1 = ram 1 ∧ t.ram 0x0b = ram 0x0b ∧
  t.ram 0x6d6 = ram 0x6d6 ∧ t.ram 0x86 = ram 0x86 ∧
  t.ram 0xce = ram 0xce &&& 0xf0

set_option maxHeartbeats 4000000 in
theorem land_reaches_pipe (m : Nat) (sp p x y : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x5D44 landPlyrCode)
    (hj : CodeAt prg 0x5EC4 landCalleesCode)
    (hI : (p &&& 4 == 0) = false) :
    ∃ j t, ((CPU.runTo (σ := Plain) 0xDEE8 (m + 40)).run
      ⟨⟨0xDD44, 0x10, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo 0xDEE8 (j + m)).run t).2 ∧ PipeCallerSummary ram prg t := by
  simp only [CodeAt, landPlyrCode, UInt16.reduceAdd] at hc
  simp only [CodeAt, landCalleesCode, UInt16.reduceAdd] at hj
  generalize hr : ((CPU.runTo (σ := Plain) 0xDEE8 (m + 40)).run
      ⟨⟨0xDD44, 0x10, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  sym_run hr [hc, hj, hI] until 57064
  all_goals
    intros
    clear hc hj
    subst hr
    reach_finish [PipeCallerSummary]

/-- With pipe-top left tile `$10`, non-rising Mario, no active jumpspring,
and feet in the landing band, the existing foot checker selects LandPlyr.
The caller still has to establish these values from real collision probes. -/
theorem pipe_tile_selects_landing (ram : UInt16 → UInt8)
    (hspd : ram 0x9f < 0x80) (hjump : ram 0x70e = 0)
    (hrow : ram 4 < 5) : footExit 0x10 ram = 0xDD44 := by
  simp only [footExit, climbable, climbExt]
  simp only [hjump, bne]
  bv_decide

/-- The scratch foot tiles and Down bit survive the landing fragment, so
`WarpDestination` sees its exact pipe-entry guard at `$DEE8`. -/
theorem pipe_guard_at_entry (ram : UInt16 → UInt8) (t : Plain)
    (prg : UInt16 → UInt8) (h : PipeCallerSummary ram prg t)
    (hdown : ram 0x0b &&& 4 != 0) (hright : ram 0 = 0x11)
    (hleft : ram 1 = 0x10) :
    WarpDestination.pipeEntry t.ram = true := by
  rcases h with ⟨_, _, _, _, h0, h1, hd, _, _, _⟩
  simp [WarpDestination.pipeEntry, h0, h1, hd, hdown, hright, hleft]

/-- At the matched `$DEE8` cutpoint, reuse the existing destination proof.
This is conditional on the preceding foot-probe values and does not yet
establish that an arbitrary legal controller frame reaches LandPlyr. -/
theorem destination_from_pipe_entry (ram : UInt16 → UInt8) (t : Plain)
    (h : PipeCallerSummary ram WarpDestination.actualPrg t) :
    WarpDestination.Summary t.regs.s t.ram WarpDestination.actualPrg
      (WarpDestination.run
        ⟨⟨0xDEE8, t.regs.a, t.regs.x, t.regs.y, t.regs.s, t.regs.p⟩,
         t.ram, WarpDestination.actualPrg, t.cyc, false⟩) := by
  rcases h with ⟨_, _, _, hI, _, _, _, _, _, _⟩
  exact WarpDestination.handlePipeEntry_rom
    t.regs.a t.regs.x t.regs.y t.regs.s t.regs.p t.ram t.cyc
    (by bv_decide)

theorem rom_land : CodeAt WarpDestination.actualPrg 0x5D44 landPlyrCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_land_callees : CodeAt WarpDestination.actualPrg 0x5EC4 landCalleesCode :=
  codeAt_of_matches _ _ _ (by native_decide)

end Smb.Routine.PositivePipeCaller
