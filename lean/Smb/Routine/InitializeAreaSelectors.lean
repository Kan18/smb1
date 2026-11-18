import Smb.Routine.InitializeAreaValues

/-!
# `InitializeArea`: only the selectors matter

`initAreaRam_selectors`: two RAMs that agree on `iaSel`, with the header pointer in ROM, agree at the end on every byte that
`InitializeArea` resets or writes. The other bytes are kept (`initAreaRam_keep`), so an old byte outside `iaSel` can influence
nothing but itself. Without the pointer condition the header bytes can be read from RAM, and the plain machine flags
the addresses it cannot serve (`initAreaBad`). `rom_initializeArea` checks the code bytes against the game's ROM.
-/
namespace Smb.Routine
set_option linter.unusedVariables false
noncomputable section

def iaG5 (sp : UInt8) (i : UInt16) : Bool := iaG4 sp i || i == 0x774

theorem iaG4_E7 (sp : UInt8) : iaG4 sp 0xE7 = true := by
  simp only [iaG4, iaG3, iaCleared]; bv_decide (config := { enums := false })
theorem iaG4_E8 (sp : UInt8) : iaG4 sp 0xE8 = true := by
  simp only [iaG4, iaG3, iaCleared]; bv_decide (config := { enums := false })

theorem iaR5_agree (s sp : UInt8) (R1 R2 prg : UInt16 → UInt8) (h : ∀ i, iaG4 sp i = true → R1 i = R2 i) (i : UInt16)
    (hi : iaG4 sp i = true) (hp : 0x80 ≤ R1 0xE8) : iaDB_ram s R1 prg i = iaDB_ram s R2 prg i := by
  have e1 := h 0xE7 (iaG4_E7 sp)
  have e2 := h 0xE8 (iaG4_E8 sp)
  have e := h i hi
  rw [e2] at hp
  simp only [iaDB_ram, iaDB_c0, e, e1, e2]
  clear e e1 e2 h hi
  revert hp
  bv_decide (config := { enums := false })

theorem iaR6_agree (s sp : UInt8) (R1 R2 prg : UInt16 → UInt8) (h : ∀ i, iaG4 sp i = true → R1 i = R2 i) (i : UInt16)
    (hi : iaG4 sp i = true) (hp : (0x80 ≤ R1 0xE8 && !(R1 0xE8 == 0xFF && R1 0xE7 == 0xFF)) = true) :
    iaDC_ram iaDB_y s R1 prg i = iaDC_ram iaDB_y s R2 prg i := by
  have e1 := h 0xE7 (iaG4_E7 sp)
  have e2 := h 0xE8 (iaG4_E8 sp)
  have e := h i hi
  rw [e1, e2] at hp
  simp only [iaDC_ram, iaDC_c0, iaDB_y, e, e1, e2]
  clear e e1 e2 h hi
  revert hp
  bv_decide (config := { enums := false })

theorem iaR7_agree (sp : UInt8) (R1 R2 : UInt16 → UInt8) (h : ∀ i, iaG4 sp i = true → R1 i = R2 i) (i : UInt16)
    (hi : iaG4 sp i = true) : iaDD_ram R1 i = iaDD_ram R2 i := by
  have e1 := h 0xE7 (iaG4_E7 sp)
  have e2 := h 0xE8 (iaG4_E8 sp)
  have e := h i hi
  simp only [iaDD_ram, e, e1, e2]

theorem iaEnd_agree (sp : UInt8) (R1 R2 : UInt16 → UInt8) (h : ∀ i, iaG4 sp i = true → R1 i = R2 i) (i : UInt16)
    (hi : iaG5 sp i = true) : iaEnd_ram R1 i = iaEnd_ram R2 i := by
  have sel : ∀ a : UInt16, iaSel a = true → iaG4 sp a = true := by
    intro a ha
    simp only [iaG4, iaG3, ha, Bool.or_true, Bool.true_or]
  have e1 := h 0x76A (sel _ (by decide))
  have e2 := h 0x75F (sel _ (by decide))
  have e3 := h 0x75C (sel _ (by decide))
  have e4 := h 0x75B (sel _ (by decide))
  have e5 := h 0x772 (sel _ (by decide))
  simp only [iaG5, Bool.or_eq_true] at hi
  rcases hi with hi | hi
  · have e := h i hi
    simp only [iaEnd_ram, iaEnd_c0, iaEnd_c1, iaEnd_c2, iaEnd_c3, iaEnd_c4, iaEnd_c5, iaEnd_c6, iaEnd_c7, iaEnd_c8,
      e, e1, e2, e3, e4, e5]
  · have e6 : i = 0x774 := by simpa using hi
    subst e6
    simp only [iaEnd_ram, iaEnd_c0, iaEnd_c1, iaEnd_c2, iaEnd_c3, iaEnd_c4, iaEnd_c5, iaEnd_c6, iaEnd_c7, iaEnd_c8,
      e1, e2, e3, e4, e5]
    clear e1 e2 e3 e4 e5 sel h
    bv_decide (config := { enums := false })

theorem iaR5_E (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16) (hw : (i == 0xE7 || i == 0xE8) = true) :
    iaR5 sp ram prg i = iaR4 sp ram prg i := by
  apply iaDB_ram_frame
  simp only [iaDB_writes, iaDA_s]
  revert hw
  bv_decide (config := { enums := false })

/-- **Only the selectors matter.** -/
theorem initAreaRam_selectors (sp : UInt8) (r1 r2 prg : UInt16 → UInt8) (hsel : ∀ i, iaSel i = true → r1 i = r2 i)
    (hp : iaHdrOk sp r1 prg = true) (i : UInt16)
    (hi : (iaCleared i || iaTimer i || iaLate sp i || iaSel i) = true) :
    initAreaRam sp r1 prg i = initAreaRam sp r2 prg i := by
  have h2 : ∀ j, (iaCleared j || iaSel j) = true → iaR2 sp r1 j = iaR2 sp r2 j := iaR2_agree sp r1 r2 hsel
  have h3 : ∀ j, iaG3 sp j = true → iaR3 sp r1 j = iaR3 sp r2 j := iaR3_agree sp _ _ h2
  have h4 : ∀ j, iaG4 sp j = true → iaR4 sp r1 prg j = iaR4 sp r2 prg j := iaR4_agree sp _ _ prg h3
  simp only [iaHdrOk, Bool.and_eq_true] at hp
  have h5 : ∀ j, iaG4 sp j = true → iaR5 sp r1 prg j = iaR5 sp r2 prg j :=
    fun j hj => iaR5_agree (iaDA_s sp) sp _ _ prg h4 j hj (of_decide_eq_true hp.1)
  have hp5 : (0x80 ≤ iaR5 sp r1 prg 0xE8 && !(iaR5 sp r1 prg 0xE8 == 0xFF && iaR5 sp r1 prg 0xE7 == 0xFF)) = true := by
    rw [iaR5_E sp r1 prg 0xE8 (by decide), iaR5_E sp r1 prg 0xE7 (by decide)]
    simp only [Bool.and_eq_true]
    exact hp
  have h6 : ∀ j, iaG4 sp j = true → iaR6 sp r1 prg j = iaR6 sp r2 prg j :=
    fun j hj => iaR6_agree (iaDA_s sp) sp _ _ prg h5 j hj hp5
  have h7 : ∀ j, iaG4 sp j = true → iaR7 sp r1 prg j = iaR7 sp r2 prg j :=
    fun j hj => iaR7_agree sp _ _ h6 j hj
  apply iaEnd_agree sp _ _ h7
  simp only [iaG5, iaG4, iaG3, iaLate, iaLate7, iaCleared, iaTimer, iaSel, iaStk] at hi ⊢
  revert hi
  bv_decide (config := { enums := false })

/-- With the header pointer in ROM, the plain machine serves every access of `InitializeArea`. -/
theorem initAreaBad_eq (sp : UInt8) (ram prg : UInt16 → UInt8) (bad : Bool) (hp : iaHdrOk sp ram prg = true) :
    initAreaBad sp ram prg bad = bad := by
  simp only [iaHdrOk] at hp
  simp only [initAreaBad, iaDC_bad, iaDB_bad, iaDB_y, iaR5_E sp ram prg 0xE7 (by decide), iaR5_E sp ram prg 0xE8 (by decide)]
  revert hp
  generalize iaR4 sp ram prg 0xE7 = lo
  generalize iaR4 sp ram prg 0xE8 = hi
  cases bad <;> bv_decide (config := { enums := false })

/-- The code in these theorems is the game's (compiled evaluation). -/
theorem rom_initializeArea :
    let g : UInt16 → UInt8 := fun a => Smb.prg.get! (a &&& 0x7FFF).toNat
    CodeAt g 0x0FE4 iaHeadCode ∧ CodeAt g 0x10CC initMemCode ∧ CodeAt g 0x0FE9 iaMidCode ∧ CodeAt g 0x3038 getScreenPosCode ∧
    CodeAt g 0x1C09 getAreaTypeCode ∧ CodeAt g 0x1C22 getAreaDataCode ∧ CodeAt g 0x1032 iaEndCode :=
  ⟨codeAt_of_matches _ _ _ (by native_decide), codeAt_of_matches _ _ _ (by native_decide),
   codeAt_of_matches _ _ _ (by native_decide), codeAt_of_matches _ _ _ (by native_decide),
   codeAt_of_matches _ _ _ (by native_decide), codeAt_of_matches _ _ _ (by native_decide),
   codeAt_of_matches _ _ _ (by native_decide)⟩

-- The stack bound is tight for the first `rts`: at `$60` the low return byte is cleared.
theorem initArea_low_return_cleared (ram : UInt16 → UInt8) : iaR2 0x60 ram (iaStk (0x60 - 2 + 1)) = 0 := by
  simp only [iaR2, initMemRam, iaPushRam, iaStk]
  bv_decide (config := { enums := false })


end
end Smb.Routine
