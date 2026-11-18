import Smb.Routine.ScrollDefs

namespace Smb.Routine

def scrollPostLeft (b : UInt8) : Bool := b &&& 0x80 != 0
def scrollPostRight (b : UInt8) : Bool := b &&& 0x80 == 0 && b &&& 0x20 != 0
def scrollPostRam (b : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  let l := scrollPostLeft b
  let r := scrollPostRight b
  bif i == 0x3A1 then 0
  else bif i == 0 then b
  else bif (l || r) && i == 0x86 then
    (bif l then ram 0x71C else ram 0x71D - 0x10)
  else bif (l || r) && i == 0x6D then
    (bif l then ram 0x71A else ram 0x71B - (bif ram 0x71D < 0x10 then 1 else 0))
  else bif ((l && ram 0x0C != 1) || (r && ram 0x0C != 2)) && i == 0x57 then 0
  else ram i

def scrollPostCycles (b : UInt8) (ram : UInt16 → UInt8) : UInt64 :=
  bif scrollPostLeft b then 10 + 29 + (bif ram 0x0C != 1 then 7 else 3) + 6
  else bif scrollPostRight b then 18 + 29 + (bif ram 0x0C != 2 then 7 else 3) + 6
  else 19 + 6

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
theorem scrollPost_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xB005 ≤ a && a ≤ 0xB033) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x2F93 scrollCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 40)).run
      ⟨⟨0xB005, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run
        ⟨⟨0xB033, 0, x, bif scrollPostLeft a then 0 else 1, sp, p'⟩,
          scrollPostRam a ram, prg, cyc + scrollPostCycles a ram, bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, scrollCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run
    ⟨⟨0xB005, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI] until 45107
  all_goals
    intros
    clear hcode
    subst hrun
    call_finish [scrollPostRam, scrollPostCycles, scrollPostLeft, scrollPostRight]

end Smb.Routine
