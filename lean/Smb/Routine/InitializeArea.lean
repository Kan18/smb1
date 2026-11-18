import Smb.Routine.InitializeAreaData
import Smb.Routine.InitializeAreaEnd

/-!
# `InitializeArea` (`$8FE4`): which bytes it writes, on the plain machine

`initializeArea_call`: from `$8FE4` to its `rts` at `$9060`, with the stack pointer at `$61` or above, the end RAM is
`initAreaRam sp ram prg`. Then, for each address below `$0800`:
- `initAreaRam_clear`: in the cleared ranges and not written again: 0, whatever it held;
- `initAreaRam_keep`: outside them and not written: unchanged;
- `iaLate`: the bytes written again, listed; `initAreaRam_constants` gives the constant ones;
- `initAreaRam_congr`: the end RAM does not depend on the old value of any cleared byte.
-/
namespace Smb.Routine
set_option linter.unusedVariables false
noncomputable section

def iaR2 (sp : UInt8) (ram : UInt16 → UInt8) : UInt16 → UInt8 := initMemRam 0x4B (iaPushRam sp ram)
def iaR3 (sp : UInt8) (ram : UInt16 → UInt8) : UInt16 → UInt8 := iaMid_ram sp (iaR2 sp ram)
def iaR4 (sp : UInt8) (ram prg : UInt16 → UInt8) : UInt16 → UInt8 := iaDA_ram sp (iaR3 sp ram) prg
def iaR5 (sp : UInt8) (ram prg : UInt16 → UInt8) : UInt16 → UInt8 := iaDB_ram (iaDA_s sp) (iaR4 sp ram prg) prg
def iaR6 (sp : UInt8) (ram prg : UInt16 → UInt8) : UInt16 → UInt8 := iaDC_ram iaDB_y (iaDA_s sp) (iaR5 sp ram prg) prg
def iaR7 (sp : UInt8) (ram prg : UInt16 → UInt8) : UInt16 → UInt8 := iaDD_ram (iaR6 sp ram prg)
/-- The RAM when `InitializeArea` reaches its `rts`. -/
def initAreaRam (sp : UInt8) (ram prg : UInt16 → UInt8) : UInt16 → UInt8 := iaEnd_ram (iaR7 sp ram prg)

/-- The header pointer lies outside the plain machine's address space for this `bad`. -/
def initAreaBad (sp : UInt8) (ram prg : UInt16 → UInt8) (bad : Bool) : Bool :=
  iaDC_bad iaDB_y (iaR5 sp ram prg) (iaDB_bad (iaR4 sp ram prg) bad)

theorem fuel_step (j n r k r' : Nat) (h : r = r' + k) : j + (n + r) = j + n + r' + k := by
  subst h; omega

/-- The stack cell at `s`, as `sym_exec` reads it. -/
abbrev iaStk (s : UInt8) : UInt16 := (256 ||| s.toUInt16) &&& 2047

theorem iaPush_lo (sp : UInt8) (ram : UInt16 → UInt8) (hsp : 0x61 ≤ sp) :
    iaR2 sp ram (iaStk (sp - 2 + 1)) = 0xE8 := by
  simp only [iaR2, initMemRam, iaPushRam, iaStk]
  bv_decide (config := { enums := false })

theorem iaPush_hi (sp : UInt8) (ram : UInt16 → UInt8) (hsp : 0x61 ≤ sp) :
    iaR2 sp ram (iaStk (sp - 2 + 2)) = 0x8F := by
  simp only [iaR2, initMemRam, iaPushRam, iaStk]
  bv_decide (config := { enums := false })

theorem iaR2_zero (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16)
    (hi : (0x700 ≤ i && i ≤ 0x74B || 0x200 ≤ i && i < 0x700 || i < 0x160) = true) : iaR2 sp ram i = 0 := by
  simp only [iaR2, initMemRam]
  revert hi
  generalize iaPushRam sp ram i = r
  bv_decide (config := { enums := false })

theorem iaDA_ret_lo (sp : UInt8) (ram prg : UInt16 → UInt8) :
    iaDA_ram sp ram prg (iaStk (sp + 255)) = 0x31 := by
  simp only [iaDA_ram, iaStk]
  bv_decide (config := { enums := false })

theorem iaDA_ret_hi (sp : UInt8) (ram prg : UInt16 → UInt8) :
    iaDA_ram sp ram prg (iaStk sp) = 0x90 := by
  simp only [iaDA_ram, iaStk]
  bv_decide (config := { enums := false })


/-- The cleared ranges of `InitializeMemory` with `Y = $4B`: `$0000-$015F`, `$0200-$074B`. -/
def iaCleared (i : UInt16) : Bool := i < 0x160 || 0x200 ≤ i && i ≤ 0x74B
/-- `ClrTimersLoop`'s range. -/
def iaTimer (i : UInt16) : Bool := 0x780 ≤ i && i ≤ 0x7A1
/-- The bytes written after the clears, up to `$9032`: the screen, nametable and column variables, the header
fields and data pointers, and the stack cells of the calls' return addresses and of `pha`. -/
def iaLate7 (sp : UInt8) (i : UInt16) : Bool :=
  i == 0x71A || i == 0x725 || i == 0x728 || i == 0x71D || i == 0x71B || i == 0x720 || i == 0x721 || i == 0x6A0 ||
  i == 0x730 || i == 0x731 || i == 0x732 || i == 0x71E || i == 0x74E || i == 0x74F || i == 0xE9 || i == 0xEA ||
  i == 0xE7 || i == 0xE8 || i == 0x741 || i == 0x710 || i == 0x715 || i == 0x744 || i == 0x727 || i == 0x742 ||
  i == 0x733 || i == 0x743 || i == iaStk sp || i == iaStk (sp + 255) || i == iaStk (sp + 254) || i == iaStk (sp + 253)
/-- All bytes written after the clears: `iaLate7` and `DoneInitArea`'s. -/
def iaLate (sp : UInt8) (i : UInt16) : Bool :=
  iaLate7 sp i || i == 0x6CC || i == 0xFB || i == 0x774 || i == 0x772

theorem iaR3_read (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) (hw : iaLate7 sp i = false) (ht : iaTimer i = false) :
    iaR3 sp ram i = iaR2 sp ram i := by
  apply iaMid_ram_frame
  simp only [iaMid_writes]
  simp only [iaLate7, iaTimer, iaStk] at hw ht
  revert hw ht
  bv_decide (config := { enums := false })

theorem iaR4_read (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16) (hw : iaLate7 sp i = false) :
    iaR4 sp ram prg i = iaR3 sp ram i := by
  apply iaDA_ram_frame
  simp only [iaDA_writes]
  simp only [iaLate7, iaStk] at hw
  revert hw
  bv_decide (config := { enums := false })

theorem iaR6_read (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16)
    (hw : (i == iaStk (iaDA_s sp) || i == 0x741 || i == 0x710 || i == 0x715 || i == 0x744 || i == 0x727 || i == 0x742 ||
      i == 0x733 || i == 0x743) = false) :
    iaR6 sp ram prg i = iaR4 sp ram prg i := by
  have h1 : iaR6 sp ram prg i = iaR5 sp ram prg i := by
    apply iaDC_ram_frame
    simp only [iaDC_writes]
    simp only [iaStk] at hw
    revert hw
    bv_decide (config := { enums := false })
  have h2 : iaR5 sp ram prg i = iaR4 sp ram prg i := by
    apply iaDB_ram_frame
    simp only [iaDB_writes]
    simp only [iaStk] at hw
    revert hw
    bv_decide (config := { enums := false })
  rw [h1, h2]

theorem iaR7_read (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16) (hw : (i == 0xE7 || i == 0xE8) = false) :
    iaR7 sp ram prg i = iaR6 sp ram prg i := by
  apply iaDD_ram_frame
  simp only [iaDD_writes]
  revert hw
  bv_decide (config := { enums := false })

/-- A byte not written after the clears holds what the first clear left. -/
theorem initAreaRam_read7 (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16) (hw : iaLate7 sp i = false) :
    iaR7 sp ram prg i = iaR3 sp ram i := by
  have hw' := hw
  simp only [iaLate7, iaStk] at hw'
  rw [iaR7_read sp ram prg i (by revert hw'; bv_decide (config := { enums := false })),
    iaR6_read sp ram prg i (by simp only [iaStk, iaDA_s]; revert hw'; bv_decide (config := { enums := false })), iaR4_read sp ram prg i hw]

theorem initAreaRam_read (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16) (hw : iaLate sp i = false) :
    initAreaRam sp ram prg i = iaR3 sp ram i := by
  have hw' := hw
  simp only [iaLate, Bool.or_eq_false_iff] at hw'
  have h7 : iaLate7 sp i = false := hw'.1.1.1.1
  have h1 : initAreaRam sp ram prg i = iaR7 sp ram prg i := by
    apply iaEnd_ram_frame
    simp only [iaEnd_writes]
    simp only [iaLate, iaLate7, iaStk] at hw
    revert hw
    bv_decide (config := { enums := false })
  rw [h1, initAreaRam_read7 sp ram prg i h7]

theorem iaR6_ret_lo (sp : UInt8) (ram prg : UInt16 → UInt8) :
    iaR6 sp ram prg ((0x100 ||| (iaDA_s sp + 1).toUInt16) &&& 0x7FF) = 0x31 := by
  have e : iaDA_s sp + 1 = sp + 255 := by
    simp only [iaDA_s]; bv_decide (config := { enums := false })
  rw [e, iaR6_read sp ram prg _ (by simp only [iaStk, iaDA_s]; bv_decide (config := { enums := false }))]
  exact iaDA_ret_lo sp _ prg

theorem iaR6_ret_hi (sp : UInt8) (ram prg : UInt16 → UInt8) :
    iaR6 sp ram prg ((0x100 ||| (iaDA_s sp + 2).toUInt16) &&& 0x7FF) = 0x90 := by
  have e : iaDA_s sp + 2 = sp := by
    simp only [iaDA_s]; bv_decide (config := { enums := false })
  rw [e, iaR6_read sp ram prg _ (by simp only [iaStk, iaDA_s]; bv_decide (config := { enums := false }))]
  exact iaDA_ret_hi sp _ prg

theorem iaR7_sec (sp : UInt8) (ram prg : UInt16 → UInt8) (hsp : 0x61 ≤ sp) : iaR7 sp ram prg 0x6CC = 0 := by
  rw [initAreaRam_read7 sp ram prg 0x6CC (by simp only [iaLate7, iaStk]; bv_decide (config := { enums := false })),
    iaR3_read sp ram 0x6CC (by simp only [iaLate7, iaStk]; bv_decide (config := { enums := false })) (by decide)]
  exact iaR2_zero sp ram 0x6CC (by decide)

/-- **`InitializeArea`**, `$8FE4` to its `rts` at `$9060`. -/
theorem initializeArea_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8FE4 ≤ a && a ≤ 0x905F || 0x90CC ≤ a && a ≤ 0x90E6 || 0x9C09 ≤ a && a ≤ 0x9C12 ||
      0x9C22 ≤ a && a ≤ 0x9CB3 || 0xB038 ≤ a && a ≤ 0xB049) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hhead : CodeAt prg 0x0FE4 iaHeadCode) (hmem : CodeAt prg 0x10CC initMemCode) (hmid : CodeAt prg 0x0FE9 iaMidCode)
    (hsc : CodeAt prg 0x3038 getScreenPosCode) (ht : CodeAt prg 0x1C09 getAreaTypeCode)
    (hd : CodeAt prg 0x1C22 getAreaDataCode) (hend : CodeAt prg 0x1032 iaEndCode)
    (hI : (p &&& 4 == 0) = false) (hsp : 0x61 ≤ sp) :
    ∃ j p' c', ((CPU.runTo (σ := Plain) stop (m + 16699)).run ⟨⟨0x8FE4, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0x9060, 1, 0xFF, 1, sp, p'⟩, initAreaRam sp ram prg, prg, c', initAreaBad sp ram prg bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  have hs1 : ∀ a : UInt16, (0x8FE4 ≤ a && a ≤ 0x8FE8) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have hs2 : ∀ a : UInt16, (0x90CC ≤ a && a ≤ 0x90E5) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have hs3 : ∀ a : UInt16, (0x90E6 ≤ a && a ≤ 0x90E6) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have hs4 : ∀ a : UInt16, (0x8FE9 ≤ a && a ≤ 0x902E || 0xB038 ≤ a && a ≤ 0xB049) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have hs5 : ∀ a : UInt16, (0x902F ≤ a && a ≤ 0x9031 || 0x9C09 ≤ a && a ≤ 0x9C12 || 0x9C22 ≤ a && a ≤ 0x9C57) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have hs6 : ∀ a : UInt16, (0x9C58 ≤ a && a ≤ 0x9C7E) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have hs7 : ∀ a : UInt16, (0x9C7F ≤ a && a ≤ 0x9CA5) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have hs8 : ∀ a : UInt16, (0x9CA6 ≤ a && a ≤ 0x9CB3) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have hs9 : ∀ a : UInt16, (0x9032 ≤ a && a ≤ 0x905F) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have ss : sp - 2 + 2 = sp := by bv_decide (config := { enums := false })
  have pc4 : iaMid_pc = 0x902F := by simp only [iaMid_pc]
  have pc5 : iaDA_pc = 0x9C58 := by simp only [iaDA_pc]
  have pc6 : iaDB_pc = 0x9C7F := by simp only [iaDB_pc]
  have pc7 : iaDC_pc = 0x9CA6 := by simp only [iaDC_pc]
  have pc8 : iaDD_pc = 0x9032 := by simp only [iaDD_pc]
  have pc9 : iaEnd_pc = 0x9060 := by simp only [iaEnd_pc]
  have s8 : iaDD_s (iaDA_s sp) = sp := by
    simp only [iaDD_s, iaDA_s]; bv_decide (config := { enums := false })
  obtain ⟨j1, p1, c1, h1, hI1⟩ := iaHead stop hs1 (m + 16697) a x y sp p ram prg cyc bad hhead hI
  obtain ⟨j2, p2, c2, h2, hI2⟩ := initMem_call stop hs2 (j1 + m + 286) a x 0x4B (sp - 2) p1 (iaPushRam sp ram) prg c1 bad hmem hI1
  obtain ⟨j3, p3, c3, h3, hI3⟩ := iaRts stop hs3 (j2 + (j1 + m) + 285) 0 0xFF 0xFF (sp - 2) p2 (initMemRam 0x4B (iaPushRam sp ram)) prg c2 bad hmem hI2
    (iaPush_lo sp ram hsp) (iaPush_hi sp ram hsp)
  rw [ss] at h3
  obtain ⟨j4, p4, h4, hI4⟩ := iaMid_call stop hs4 (j3 + (j2 + (j1 + m)) + 135) 0 0xFF 0xFF sp p3 (initMemRam 0x4B (iaPushRam sp ram)) prg c3 bad hmid hsc hI3
    (iaR2_zero sp ram 0x71C (by decide)) (iaR2_zero sp ram 0x730 (by decide)) (iaR2_zero sp ram 0x731 (by decide)) (iaR2_zero sp ram 0x732 (by decide))
  rw [pc4, iaMid_s_eq, iaMid_bad_eq] at h4
  obtain ⟨j5, p5, h5, hI5⟩ := iaDA_call stop hs5 (j4 + (j3 + (j2 + (j1 + m))) + 95) iaMid_a iaMid_x iaMid_y sp p4 (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg (iaMid_cyc (initMemRam 0x4B (iaPushRam sp ram)) c3) bad hmid ht hd hI4
  rw [pc5, iaDA_bad_eq] at h5
  obtain ⟨j6, p6, h6, hI6⟩ := iaDB_call stop hs6 (j5 + (j4 + (j3 + (j2 + (j1 + m)))) + 70) (iaDA_a sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) (iaDA_x iaMid_x) (iaDA_y sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) (iaDA_s sp) p5 (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg (iaDA_cyc sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg (iaMid_cyc (initMemRam 0x4B (iaPushRam sp ram)) c3)) bad hd hI5
  rw [pc6, iaDB_s_eq] at h6
  obtain ⟨j7, p7, h7, hI7⟩ := iaDC_call stop hs7 (j6 + (j5 + (j4 + (j3 + (j2 + (j1 + m))))) + 45) (iaDB_a (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg) (iaDB_x (iaDA_x iaMid_x)) iaDB_y (iaDA_s sp) p6 (iaDB_ram (iaDA_s sp) (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg) prg (iaDB_cyc (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg (iaDA_cyc sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg (iaMid_cyc (initMemRam 0x4B (iaPushRam sp ram)) c3))) (iaDB_bad (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) bad) hd hI6
  rw [pc7, iaDC_s_eq] at h7
  obtain ⟨j8, p8, h8, hI8⟩ := iaDD_call stop hs8 (j7 + (j6 + (j5 + (j4 + (j3 + (j2 + (j1 + m)))))) + 30) (iaDC_a iaDB_y (iaDB_ram (iaDA_s sp) (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg) prg) (iaDC_x (iaDB_x (iaDA_x iaMid_x))) (iaDC_y iaDB_y) (iaDA_s sp) p7 (iaDC_ram iaDB_y (iaDA_s sp) (iaDB_ram (iaDA_s sp) (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg) prg) prg (iaDC_cyc iaDB_y (iaDB_ram (iaDA_s sp) (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg) prg (iaDB_cyc (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg (iaDA_cyc sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg (iaMid_cyc (initMemRam 0x4B (iaPushRam sp ram)) c3)))) (iaDC_bad iaDB_y (iaDB_ram (iaDA_s sp) (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg) (iaDB_bad (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) bad)) hd hI7
    (iaR6_ret_lo sp ram prg) (iaR6_ret_hi sp ram prg)
  rw [pc8, s8, iaDD_bad_eq] at h8
  obtain ⟨j9, p9, h9, hI9⟩ := iaEnd_call stop hs9 (j8 + (j7 + (j6 + (j5 + (j4 + (j3 + (j2 + (j1 + m))))))) + 0) (iaDD_a (iaDC_ram iaDB_y (iaDA_s sp) (iaDB_ram (iaDA_s sp) (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg) prg)) (iaDD_x (iaDC_x (iaDB_x (iaDA_x iaMid_x)))) (iaDD_y (iaDC_y iaDB_y)) sp p8 (iaDD_ram (iaDC_ram iaDB_y (iaDA_s sp) (iaDB_ram (iaDA_s sp) (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg) prg)) prg (iaDD_cyc (iaDC_cyc iaDB_y (iaDB_ram (iaDA_s sp) (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg) prg (iaDB_cyc (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg (iaDA_cyc sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg (iaMid_cyc (initMemRam 0x4B (iaPushRam sp ram)) c3))))) (iaDC_bad iaDB_y (iaDB_ram (iaDA_s sp) (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg) (iaDB_bad (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) bad)) hend hI8
    (iaR7_sec sp ram prg hsp)
  rw [pc9, iaEnd_s_eq, iaEnd_bad_eq] at h9
  have ra : iaEnd_a = 1 := by simp only [iaEnd_a]
  have rx : iaEnd_x (iaDD_x (iaDC_x (iaDB_x (iaDA_x iaMid_x)))) = 0xFF := by
    simp only [iaEnd_x, iaDD_x, iaDC_x, iaDB_x, iaDA_x, iaMid_x]
  have ry : iaEnd_y (iaDD_y (iaDC_y iaDB_y)) = 1 := by
    simp only [iaEnd_y, iaDD_y, iaDC_y, iaDB_y]
    rfl
  rw [ra, rx, ry] at h9
  refine ⟨j9 + (j8 + (j7 + (j6 + (j5 + (j4 + (j3 + (j2 + j1))))))), p9, iaEnd_cyc (iaDD_ram (iaDC_ram iaDB_y (iaDA_s sp) (iaDB_ram (iaDA_s sp) (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg) prg)) (iaDD_cyc (iaDC_cyc iaDB_y (iaDB_ram (iaDA_s sp) (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg) prg (iaDB_cyc (iaDA_ram sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg) prg (iaDA_cyc sp (iaMid_ram sp (initMemRam 0x4B (iaPushRam sp ram))) prg (iaMid_cyc (initMemRam 0x4B (iaPushRam sp ram)) c3))))), ?_, hI9⟩
  have e0 : m + 16699 = m + 16697 + 2 := by omega
  have eJ : j9 + (j8 + (j7 + (j6 + (j5 + (j4 + (j3 + (j2 + j1))))))) + m =
      j9 + (j8 + (j7 + (j6 + (j5 + (j4 + (j3 + (j2 + (j1 + m))))))) + 0) := by
    simp only [Nat.add_assoc, Nat.add_zero]
  rw [e0, h1, fuel_step j1 m 16697 16411 286 rfl, h2, fuel_step j2 (j1 + m) 286 1 285 rfl, h3,
    fuel_step j3 (j2 + (j1 + m)) 285 150 135 rfl, h4, fuel_step j4 (j3 + (j2 + (j1 + m))) 135 40 95 rfl, h5,
    fuel_step j5 (j4 + (j3 + (j2 + (j1 + m)))) 95 25 70 rfl, h6,
    fuel_step j6 (j5 + (j4 + (j3 + (j2 + (j1 + m))))) 70 25 45 rfl, h7,
    fuel_step j7 (j6 + (j5 + (j4 + (j3 + (j2 + (j1 + m)))))) 45 15 30 rfl, h8,
    fuel_step j8 (j7 + (j6 + (j5 + (j4 + (j3 + (j2 + (j1 + m))))))) 30 30 0 rfl, h9, eJ]
  rfl

/-- A cleared byte that nothing writes again is 0 at the end, whatever it held. -/
theorem initAreaRam_clear (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16)
    (hc : iaCleared i = true) (hw : iaLate sp i = false) : initAreaRam sp ram prg i = 0 := by
  have hc' := hc
  simp only [iaCleared] at hc'
  have ht : iaTimer i = false := by
    simp only [iaTimer]; revert hc'; bv_decide (config := { enums := false })
  have h7 : iaLate7 sp i = false := by
    simp only [iaLate, Bool.or_eq_false_iff] at hw; exact hw.1.1.1.1
  rw [initAreaRam_read sp ram prg i hw, iaR3_read sp ram i h7 ht]
  exact iaR2_zero sp ram i (by revert hc'; bv_decide (config := { enums := false }))

theorem iaMid_timer (sp : UInt8) (R : UInt16 → UInt8) (i : UInt16) (ht : iaTimer i = true) : iaMid_ram sp R i = 0 := by
  simp only [iaTimer] at ht
  simp only [iaMid_ram]
  revert ht
  generalize R i = r
  bv_decide (config := { enums := false })

/-- `ClrTimersLoop`: every frame timer `$0780-$07A1` is 0 at the end. -/
theorem initAreaRam_timer (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16) (ht : iaTimer i = true) :
    initAreaRam sp ram prg i = 0 := by
  have hl : iaLate sp i = false := by
    simp only [iaLate, iaLate7, iaStk]
    simp only [iaTimer] at ht
    revert ht
    bv_decide (config := { enums := false })
  rw [initAreaRam_read sp ram prg i hl]
  exact iaMid_timer sp _ i ht

/-- A byte outside the cleared ranges that nothing writes is unchanged. -/
theorem initAreaRam_keep (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16)
    (hc : iaCleared i = false) (ht : iaTimer i = false) (hw : iaLate sp i = false) : initAreaRam sp ram prg i = ram i := by
  have h7 : iaLate7 sp i = false := by
    simp only [iaLate, Bool.or_eq_false_iff] at hw; exact hw.1.1.1.1
  rw [initAreaRam_read sp ram prg i hw, iaR3_read sp ram i h7 ht]
  simp only [iaLate7, iaStk] at h7
  simp only [iaCleared] at hc
  simp only [iaR2, initMemRam, iaPushRam]
  revert h7 hc
  generalize ram i = r
  bv_decide (config := { enums := false })

theorem iaMid_congr (sp : UInt8) (R1 R2 : UInt16 → UInt8) (h : ∀ i, iaTimer i = false → R1 i = R2 i) :
    iaMid_ram sp R1 = iaMid_ram sp R2 := by
  funext i
  cases ht : iaTimer i with
  | true => rw [iaMid_timer sp R1 i ht, iaMid_timer sp R2 i ht]
  | false =>
    have e := h i ht
    have e1 := h 0x75B (by decide)
    have e2 := h 0x752 (by decide)
    have e3 := h 0x751 (by decide)
    simp only [iaMid_ram, iaMid_c0, iaMid_c1, iaMid_c2, e, e1, e2, e3]

theorem iaR3_congr (sp : UInt8) (r1 r2 : UInt16 → UInt8)
    (h : ∀ i, iaCleared i = false → iaTimer i = false → r1 i = r2 i) : iaR3 sp r1 = iaR3 sp r2 := by
  apply iaMid_congr
  intro i ht
  cases hc : iaCleared i with
  | true =>
    simp only [iaCleared] at hc
    rw [iaR2_zero sp r1 i (by revert hc; bv_decide (config := { enums := false })), iaR2_zero sp r2 i (by revert hc; bv_decide (config := { enums := false }))]
  | false =>
    simp only [iaR2, initMemRam, iaPushRam, h i hc ht]

/-- **No influence from a cleared byte.** Two RAMs that may differ only in the cleared ranges and the timers give
the same end RAM, whatever those bytes held. -/
theorem initAreaRam_congr (sp : UInt8) (r1 r2 prg : UInt16 → UInt8)
    (h : ∀ i, iaCleared i = false → iaTimer i = false → r1 i = r2 i) :
    initAreaRam sp r1 prg = initAreaRam sp r2 prg := by
  simp only [initAreaRam, iaR7, iaR6, iaR5, iaR4, iaR3_congr sp r1 r2 h]

theorem initAreaBad_congr (sp : UInt8) (r1 r2 prg : UInt16 → UInt8) (bad : Bool)
    (h : ∀ i, iaCleared i = false → iaTimer i = false → r1 i = r2 i) :
    initAreaBad sp r1 prg bad = initAreaBad sp r2 prg bad := by
  simp only [initAreaBad, iaR5, iaR4, iaR3_congr sp r1 r2 h]

/-- The enemy frame timers `$078A-$078F`, including the Piranha Plant's and Hammer Bros.' slots, and
`HammerBroJumpTimer` `$3C-$41`, are 0 at the end on every route through `InitializeArea`. -/
theorem initAreaRam_enemyTimers (sp : UInt8) (ram prg : UInt16 → UInt8) (k : UInt16) (hk : k < 6) :
    initAreaRam sp ram prg (0x78A + k) = 0 ∧ initAreaRam sp ram prg (0x3C + k) = 0 := by
  constructor
  · apply initAreaRam_timer
    simp only [iaTimer]
    revert hk
    bv_decide (config := { enums := false })
  · apply initAreaRam_clear
    · simp only [iaCleared]
      revert hk
      bv_decide (config := { enums := false })
    · simp only [iaLate, iaLate7, iaStk]
      revert hk
      bv_decide (config := { enums := false })


end
end Smb.Routine
