import Smb.Routine.InitializeArea

/-!
# What `InitializeArea` writes back

The values of the bytes written after the clears: `initAreaRam_constants`, `initAreaRam_pageVars`, `initAreaRam_end`.
`initAreaRam_selectors`: when the header pointer is in ROM, everything `InitializeArea` resets or writes depends on the
old RAM only through the eight selector bytes.
-/
namespace Smb.Routine
set_option linter.unusedVariables false
noncomputable section

/-- Bytes written by the header code and `DoneInitArea`. Neither segment touches the screen variables. -/
def iaDataW (sp : UInt8) (i : UInt16) : Bool :=
  i == iaStk sp || i == iaStk (sp + 255) || i == iaStk (sp + 254) || i == iaStk (sp + 253) ||
  i == 0x74E || i == 0x74F || i == 0xE9 || i == 0xEA || i == 0xE7 || i == 0xE8 ||
  i == 0x741 || i == 0x710 || i == 0x715 || i == 0x744 || i == 0x727 || i == 0x742 || i == 0x733 || i == 0x743 ||
  i == 0x6CC || i == 0xFB || i == 0x774 || i == 0x772

/-- Through everything after `iaMid`, for a byte none of it writes. -/
theorem initAreaRam_read3 (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16) (hw : iaDataW sp i = false) :
    initAreaRam sp ram prg i = iaR3 sp ram i := by
  simp only [iaDataW, iaStk] at hw
  have h1 : initAreaRam sp ram prg i = iaR7 sp ram prg i := by
    apply iaEnd_ram_frame
    simp only [iaEnd_writes]
    revert hw
    bv_decide (config := { enums := false })
  have h4 : iaR4 sp ram prg i = iaR3 sp ram i := by
    apply iaDA_ram_frame
    simp only [iaDA_writes]
    revert hw
    bv_decide (config := { enums := false })
  rw [h1, iaR7_read sp ram prg i (by revert hw; bv_decide (config := { enums := false })),
    iaR6_read sp ram prg i (by simp only [iaStk, iaDA_s]; revert hw; bv_decide (config := { enums := false })), h4]

/-- The start page: `AltEntranceControl` selects `HalfwayPage` or `EntrancePage`. -/
def iaPage (ram : UInt16 → UInt8) : UInt8 := bif ram 0x752 == 0 then ram 0x75B else ram 0x751

theorem iaR2_carried (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) (h : 0x74C ≤ i) (h' : i ≤ 0x77F) :
    iaR2 sp ram i = ram i := by
  simp only [iaR2, initMemRam, iaPushRam]
  revert h h'
  generalize ram i = r
  bv_decide (config := { enums := false })

/-- The constants. -/
theorem initAreaRam_constants (sp : UInt8) (ram prg : UInt16 → UInt8) :
    initAreaRam sp ram prg 0x730 = 0xFF ∧ initAreaRam sp ram prg 0x731 = 0xFF ∧ initAreaRam sp ram prg 0x732 = 0xFF ∧
    initAreaRam sp ram prg 0x71E = 0x0B ∧ initAreaRam sp ram prg 0x721 = 0x80 ∧ initAreaRam sp ram prg 0x71D = 0xFF ∧
    initAreaRam sp ram prg 0xFB = 0x80 ∧ initAreaRam sp ram prg 0x774 = 1 := by
  have m : ∀ i : UInt16, iaDataW sp i = false → initAreaRam sp ram prg i = iaMid_ram sp (iaR2 sp ram) i :=
    fun i h => initAreaRam_read3 sp ram prg i h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m _ (by simp only [iaDataW, iaStk]; bv_decide (config := { enums := false }))]; simp only [iaMid_ram]; bv_decide (config := { enums := false })
  · rw [m _ (by simp only [iaDataW, iaStk]; bv_decide (config := { enums := false }))]; simp only [iaMid_ram]; bv_decide (config := { enums := false })
  · rw [m _ (by simp only [iaDataW, iaStk]; bv_decide (config := { enums := false }))]; simp only [iaMid_ram]; bv_decide (config := { enums := false })
  · rw [m _ (by simp only [iaDataW, iaStk]; bv_decide (config := { enums := false }))]; simp only [iaMid_ram]; bv_decide (config := { enums := false })
  · rw [m _ (by simp only [iaDataW, iaStk]; bv_decide (config := { enums := false }))]; simp only [iaMid_ram]; bv_decide (config := { enums := false })
  · rw [m _ (by simp only [iaDataW, iaStk]; bv_decide (config := { enums := false }))]; simp only [iaMid_ram]; bv_decide (config := { enums := false })
  · simp only [initAreaRam, iaEnd_ram]; bv_decide (config := { enums := false })
  · simp only [initAreaRam, iaEnd_ram]; bv_decide (config := { enums := false })

/-- The screen, nametable and block buffer variables, from the start page. -/
theorem initAreaRam_pageVars (sp : UInt8) (ram prg : UInt16 → UInt8) :
    let P := iaPage ram
    initAreaRam sp ram prg 0x71A = P ∧ initAreaRam sp ram prg 0x725 = P ∧ initAreaRam sp ram prg 0x728 = P ∧
    initAreaRam sp ram prg 0x71B = P ∧ initAreaRam sp ram prg 0x720 = (bif P &&& 1 == 0 then 0x20 else 0x24) ∧
    initAreaRam sp ram prg 0x6A0 = (P &&& 1) <<< 4 := by
  intro P
  have m : ∀ i : UInt16, iaDataW sp i = false → initAreaRam sp ram prg i = iaMid_ram sp (iaR2 sp ram) i :=
    fun i h => initAreaRam_read3 sp ram prg i h
  have e1 := iaR2_carried sp ram 0x752 (by decide) (by decide)
  have e2 := iaR2_carried sp ram 0x75B (by decide) (by decide)
  have e3 := iaR2_carried sp ram 0x751 (by decide) (by decide)
  simp only [P, iaPage]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [m _ (by simp only [iaDataW, iaStk]; bv_decide (config := { enums := false }))] <;>
    simp only [iaMid_ram, iaMid_c0, iaMid_c1, iaMid_c2, e1, e2, e3] <;> bv_decide (config := { enums := false })

/-- A byte `InitializeArea` reads and does not write before that read, and leaves in `$07xx` above the clear. -/
theorem iaR7_carried (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16)
    (h7 : iaLate7 sp i = false) (ht : iaTimer i = false) (h : 0x74C ≤ i) (h' : i ≤ 0x77F) : iaR7 sp ram prg i = ram i := by
  rw [initAreaRam_read7 sp ram prg i h7, iaR3_read sp ram i h7 ht, iaR2_carried sp ram i h h']

/-- `DoneInitArea` and the hard mode test. -/
theorem initAreaRam_end (sp : UInt8) (ram prg : UInt16 → UInt8) (hsp : 0x61 ≤ sp) :
    initAreaRam sp ram prg 0x6CC =
      (bif ram 0x76A != 0 || 5 ≤ ram 0x75F || (ram 0x75F == 4 && 2 ≤ ram 0x75C) then 1 else 0) ∧
    initAreaRam sp ram prg 0x772 = ram 0x772 + 1 ∧
    initAreaRam sp ram prg 0x710 = (bif ram 0x75B != 0 then 2 else iaR7 sp ram prg 0x710) := by
  have e1 := iaR7_carried sp ram prg 0x76A (by simp only [iaLate7, iaStk]; bv_decide (config := { enums := false })) (by decide) (by decide) (by decide)
  have e2 := iaR7_carried sp ram prg 0x75F (by simp only [iaLate7, iaStk]; bv_decide (config := { enums := false })) (by decide) (by decide) (by decide)
  have e3 := iaR7_carried sp ram prg 0x75C (by simp only [iaLate7, iaStk]; bv_decide (config := { enums := false })) (by decide) (by decide) (by decide)
  have e4 := iaR7_carried sp ram prg 0x75B (by simp only [iaLate7, iaStk]; bv_decide (config := { enums := false })) (by decide) (by decide) (by decide)
  have e5 := iaR7_carried sp ram prg 0x772 (by simp only [iaLate7, iaStk]; bv_decide (config := { enums := false })) (by decide) (by decide) (by decide)
  have e6 := iaR7_sec sp ram prg hsp
  simp only [initAreaRam, iaEnd_ram, iaEnd_c0, iaEnd_c1, iaEnd_c2, iaEnd_c3, iaEnd_c4, iaEnd_c5, iaEnd_c6, iaEnd_c7, iaEnd_c8,
    e1, e2, e3, e4, e5, e6, bne]
  clear e1 e2 e3 e4 e5 e6
  refine ⟨?_, ?_, ?_⟩ <;> bv_decide (config := { enums := false })

/-- The eight bytes `InitializeArea` reads from the old RAM. -/
def iaSel (i : UInt16) : Bool :=
  i == 0x750 || i == 0x751 || i == 0x752 || i == 0x75B || i == 0x75C || i == 0x75F || i == 0x76A || i == 0x772

/-- The header pointer, as `$E7/$E8` hold it after `iaDA`, is in ROM, also at the second header byte. -/
def iaHdrOk (sp : UInt8) (ram prg : UInt16 → UInt8) : Bool :=
  0x80 ≤ iaR4 sp ram prg 0xE8 && !(iaR4 sp ram prg 0xE8 == 0xFF && iaR4 sp ram prg 0xE7 == 0xFF)

def iaG3 (sp : UInt8) (i : UInt16) : Bool :=
  iaCleared i || iaSel i || iaTimer i || i == iaStk sp || i == iaStk (sp + 255)
def iaG4 (sp : UInt8) (i : UInt16) : Bool :=
  iaG3 sp i || i == iaStk (sp + 254) || i == iaStk (sp + 253) || i == 0x74E || i == 0x74F

theorem iaR2_agree (sp : UInt8) (r1 r2 : UInt16 → UInt8) (hsel : ∀ i, iaSel i = true → r1 i = r2 i) (i : UInt16)
    (h : (iaCleared i || iaSel i) = true) : iaR2 sp r1 i = iaR2 sp r2 i := by
  cases hc : iaCleared i with
  | true =>
    simp only [iaCleared] at hc
    rw [iaR2_zero sp r1 i (by revert hc; bv_decide (config := { enums := false })), iaR2_zero sp r2 i (by revert hc; bv_decide (config := { enums := false }))]
  | false =>
    have hs : iaSel i = true := by simpa [hc] using h
    have e := hsel i hs
    simp only [iaR2, initMemRam, iaPushRam, e]

theorem iaR3_agree (sp : UInt8) (R1 R2 : UInt16 → UInt8) (h : ∀ i, (iaCleared i || iaSel i) = true → R1 i = R2 i) (i : UInt16)
    (hi : iaG3 sp i = true) : iaMid_ram sp R1 i = iaMid_ram sp R2 i := by
  have e1 := h 0x75B (by decide)
  have e2 := h 0x752 (by decide)
  have e3 := h 0x751 (by decide)
  cases hw : iaMid_writes sp R1 i with
  | false =>
    have hw2 : iaMid_writes sp R2 i = false := hw
    rw [iaMid_ram_frame sp R1 i hw, iaMid_ram_frame sp R2 i hw2]
    apply h
    simp only [iaMid_writes] at hw
    simp only [iaG3, iaCleared, iaTimer, iaSel, iaStk] at hi ⊢
    revert hw hi
    bv_decide (config := { enums := false })
  | true =>
    simp only [iaMid_writes] at hw
    simp only [iaMid_ram, iaMid_c0, iaMid_c1, iaMid_c2, e1, e2, e3]
    revert hw
    generalize R1 i = a
    generalize R2 i = b
    bv_decide (config := { enums := false })

/-- The ROM tables of `GetAreaDataAddrs`: an index from a byte stays out of RAM. -/
theorem rom_idx0 (y : UInt8) : decide ((40160 : UInt16) + y.toUInt16 < 8192) = false := by bv_decide (config := { enums := false })
theorem rom_idx1 (y : UInt8) : decide ((40164 : UInt16) + y.toUInt16 < 8192) = false := by bv_decide (config := { enums := false })
theorem rom_idx2 (y : UInt8) : decide ((40198 : UInt16) + y.toUInt16 < 8192) = false := by bv_decide (config := { enums := false })
theorem rom_idx3 (y : UInt8) : decide ((40232 : UInt16) + y.toUInt16 < 8192) = false := by bv_decide (config := { enums := false })
theorem rom_idx4 (y : UInt8) : decide ((40236 : UInt16) + y.toUInt16 < 8192) = false := by bv_decide (config := { enums := false })
theorem rom_idx5 (y : UInt8) : decide ((40270 : UInt16) + y.toUInt16 < 8192) = false := by bv_decide (config := { enums := false })

theorem iaR4_agree (sp : UInt8) (R1 R2 prg : UInt16 → UInt8) (h : ∀ i, iaG3 sp i = true → R1 i = R2 i) (i : UInt16)
    (hi : iaG4 sp i = true) : iaDA_ram sp R1 prg i = iaDA_ram sp R2 prg i := by
  have e1 := h 0x750 (by simp only [iaG3, iaSel]; bv_decide (config := { enums := false }))
  cases hw : iaDA_writes sp R1 prg i with
  | false =>
    have hw2 : iaDA_writes sp R2 prg i = false := hw
    rw [iaDA_ram_frame sp R1 prg i hw, iaDA_ram_frame sp R2 prg i hw2]
    apply h
    simp only [iaDA_writes] at hw
    simp only [iaG4, iaG3, iaCleared, iaTimer, iaSel, iaStk] at hi ⊢
    revert hw hi
    bv_decide (config := { enums := false })
  | true =>
    simp only [iaDA_writes] at hw
    simp only [iaDA_ram, e1, rom_idx0, rom_idx1, rom_idx2, rom_idx3, rom_idx4, rom_idx5, Bool.cond_false]
    clear e1 h hi
    revert hw
    generalize R1 i = a
    generalize R2 i = b
    bv_decide (config := { enums := false })

end
end Smb.Routine
