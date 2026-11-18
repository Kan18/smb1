import Smb.Data.ProofRom
import Smb.Summary
import Smb.Routine.Common

/-!
# `InitializeMemory` (`$90CC`): the clearing loop, by induction

`sym_run` cannot run about 1,870 iterations, so one iteration is two small executed segments
(`imTest`, `imDec`) and the loops are inductions over them.
-/
namespace Smb.Routine
set_option linter.unusedVariables false

/-- `$90CC`–`$90E6`: `InitializeMemory`. -/
def initMemCode : List UInt8 :=
  smbPrg% 0x90CC 27

/-- One iteration's effect: clear `x:y`, unless that is in `$0160-$01FF`. -/
def imClr1 (x y : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  bif !(x == 1 && 0x60 ≤ y) && i == (x.toUInt16 <<< 8 ||| y.toUInt16) then 0 else ram i

set_option maxHeartbeats 4000000 in
/-- `$90D4`: the stack test and the store, up to `SkipByte`. -/
theorem imTest (stop : UInt16) (hstop : ∀ a : UInt16, (0x90D4 ≤ a && a ≤ 0x90DD) = true → a ≠ stop)
    (m : Nat) (x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x10CC initMemCode) (hI : (p &&& 4 == 0) = false)
    (h6 : ram 6 = 0) (h7 : ram 7 = x) (hx : x ≤ 7) :
    ∃ j p' c', ((CPU.runTo (σ := Plain) stop (m + 5)).run ⟨⟨0x90D4, 0, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0x90DE, 0, x, y, sp, p'⟩, imClr1 x y ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, initMemCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 5)).run ⟨⟨0x90D4, 0, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI, h6, h7] until 0x90DE
  all_goals
    intros
    subst hrun
    subst_vars
    call_finish [imClr1]

set_option maxHeartbeats 4000000 in
/-- `$90DE`: `SkipByte`, the decrement and the loop test. -/
theorem imDec (stop : UInt16) (hstop : ∀ a : UInt16, (0x90DE ≤ a && a ≤ 0x90E2) = true → a ≠ stop)
    (m : Nat) (x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x10CC initMemCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j p' c', ((CPU.runTo (σ := Plain) stop (m + 3)).run ⟨⟨0x90DE, 0, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨bif y == 0 then 0x90E3 else 0x90D4, 0, x, y - 1, sp, p'⟩, ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, initMemCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3)).run ⟨⟨0x90DE, 0, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI] until [0x90E3, 0x90D4]
  all_goals
    intros
    subst hrun
    subst_vars
    call_finish []

/-- The byte loop's effect on page `x`, from `y` down: clear `x:0`–`x:y`, except `$0160-$01FF`. -/
def imClrBytes (x y : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  bif i >>> 8 == x.toUInt16 && i &&& 0xFF ≤ y.toUInt16 && !(x == 1 && 0x60 ≤ i &&& 0xFF) then 0 else ram i

theorem imClr1_bytes_zero (x : UInt8) (ram : UInt16 → UInt8) : imClr1 x 0 ram = imClrBytes x 0 ram := by
  funext i
  generalize hr : ram i = r
  simp only [imClr1, imClrBytes, hr]
  bv_decide (config := { enums := false })

theorem imClrBytes_succ (x y : UInt8) (hy : y ≠ 0) (ram : UInt16 → UInt8) :
    imClrBytes x (y - 1) (imClr1 x y ram) = imClrBytes x y ram := by
  funext i
  generalize hr : ram i = r
  simp only [imClr1, imClrBytes, hr]
  bv_decide (config := { enums := false })

theorem imClr1_6 (x y : UInt8) (ram : UInt16 → UInt8) (h6 : ram 6 = 0) : imClr1 x y ram 6 = 0 := by
  simp only [imClr1, h6]
  bv_decide (config := { enums := false })

theorem imClr1_7 (x y : UInt8) (ram : UInt16 → UInt8) (h7 : ram 7 = x) : imClr1 x y ram 7 = x := by
  simp only [imClr1, h7]
  bv_decide (config := { enums := false })

theorem toNat_pred (y : UInt8) (n : Nat) (hy : y.toNat = n + 1) : (y - 1).toNat = n ∧ y ≠ 0 := by
  have h0 : y ≠ 0 := by
    intro h
    subst h
    simp at hy
  have h1 : (1 : UInt8) ≤ y := by
    revert h0
    bv_decide (config := { enums := false })
  refine ⟨?_, h0⟩
  rw [UInt8.toNat_sub_of_le _ _ h1]
  simp [hy]

/-- The byte loop, by induction on `y`. -/
theorem imBytes (stop : UInt16) (hstop : ∀ a : UInt16, (0x90D4 ≤ a && a ≤ 0x90E2) = true → a ≠ stop)
    (x sp : UInt8) (prg : UInt16 → UInt8) (bad : Bool)
    (hcode : CodeAt prg 0x10CC initMemCode) (hx : x ≤ 7) (n : Nat) :
    ∀ (m : Nat) (y p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64), y.toNat = n →
    (p &&& 4 == 0) = false → ram 6 = 0 → ram 7 = x →
    ∃ j p' c', ((CPU.runTo (σ := Plain) stop (m + 8 * (n + 1))).run ⟨⟨0x90D4, 0, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0x90E3, 0, x, 0xFF, sp, p'⟩, imClrBytes x y ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  have hsT : ∀ a : UInt16, (0x90D4 ≤ a && a ≤ 0x90DD) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have hsD : ∀ a : UInt16, (0x90DE ≤ a && a ≤ 0x90E2) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  induction n with
  | zero =>
    intro m y p ram cyc hy hI h6 h7
    have hy0 : y = 0 := by
      apply UInt8.toNat_inj.mp; simpa using hy
    subst hy0
    obtain ⟨j1, p1, c1, h1, hI1⟩ := imTest stop hsT (m + 3) x 0 sp p ram prg cyc bad hcode hI h6 h7 hx
    obtain ⟨j2, p2, c2, h2, hI2⟩ := imDec stop hsD (j1 + m) x 0 sp p1 (imClr1 x 0 ram) prg c1 bad hcode hI1
    refine ⟨j2 + j1, p2, c2, ?_, hI2⟩
    have e1 : m + 8 * (0 + 1) = m + 3 + 5 := by omega
    have e2 : j1 + (m + 3) = j1 + m + 3 := by omega
    have e3 : j2 + j1 + m = j2 + (j1 + m) := by omega
    rw [e1, h1, e2, h2, e3, imClr1_bytes_zero]
    rfl
  | succ n ih =>
    intro m y p ram cyc hy hI h6 h7
    obtain ⟨hn, hy0⟩ := toNat_pred y n hy
    obtain ⟨j1, p1, c1, h1, hI1⟩ := imTest stop hsT (m + 8 * (n + 1) + 3) x y sp p ram prg cyc bad hcode hI h6 h7 hx
    obtain ⟨j2, p2, c2, h2, hI2⟩ := imDec stop hsD (j1 + m + 8 * (n + 1)) x y sp p1 (imClr1 x y ram) prg c1 bad hcode hI1
    obtain ⟨j3, p3, c3, h3, hI3⟩ := ih (j2 + (j1 + m)) (y - 1) p2 (imClr1 x y ram) c2 hn hI2
      (imClr1_6 x y ram h6) (imClr1_7 x y ram h7)
    refine ⟨j3 + (j2 + j1), p3, c3, ?_, hI3⟩
    have hb : (y == 0) = false := by simpa using hy0
    have e1 : m + 8 * (n + 1 + 1) = m + 8 * (n + 1) + 3 + 5 := by omega
    have e2 : j1 + (m + 8 * (n + 1) + 3) = j1 + m + 8 * (n + 1) + 3 := by omega
    have e3 : j2 + (j1 + m + 8 * (n + 1)) = j2 + (j1 + m) + 8 * (n + 1) := by omega
    have e4 : j3 + (j2 + j1) + m = j3 + (j2 + (j1 + m)) := by omega
    rw [e1, h1, e2, h2, hb, Bool.cond_false, e3, h3, e4, imClrBytes_succ x y hy0]

/-- `stx $07`. -/
def imStx (x : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 := bif i == 7 then x else ram i

set_option maxHeartbeats 4000000 in
/-- `$90D2`: `InitPageLoop`, `stx $07`. -/
theorem imStxRun (stop : UInt16) (hstop : ∀ a : UInt16, (0x90D2 ≤ a && a ≤ 0x90D3) = true → a ≠ stop)
    (m : Nat) (x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x10CC initMemCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j p' c', ((CPU.runTo (σ := Plain) stop (m + 1)).run ⟨⟨0x90D2, 0, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0x90D4, 0, x, y, sp, p'⟩, imStx x ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, initMemCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 1)).run ⟨⟨0x90D2, 0, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI] until 0x90D4
  all_goals
    intros
    subst hrun
    subst_vars
    call_finish [imStx]

set_option maxHeartbeats 4000000 in
/-- `$90E3`: `dex`, `bpl InitPageLoop`. -/
theorem imTail (stop : UInt16) (hstop : ∀ a : UInt16, (0x90E3 ≤ a && a ≤ 0x90E5) = true → a ≠ stop)
    (m : Nat) (x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x10CC initMemCode) (hI : (p &&& 4 == 0) = false) (hx : x ≤ 7) :
    ∃ j p' c', ((CPU.runTo (σ := Plain) stop (m + 2)).run ⟨⟨0x90E3, 0, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨bif x == 0 then 0x90E6 else 0x90D2, 0, x - 1, y, sp, p'⟩, ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, initMemCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 2)).run ⟨⟨0x90E3, 0, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI] until [0x90E6, 0x90D2]
  all_goals
    intros
    subst hrun
    subst_vars
    call_finish []

/-- The page loop's effect from page `x` with a full first page: pages `0`–`x` cleared, except `$0160-$01FF`. -/
def imClrPages (x : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  bif i >>> 8 ≤ x.toUInt16 && !(i >>> 8 == 1 && 0x60 ≤ i &&& 0xFF) then 0 else ram i

theorem imClrPages_zero (ram : UInt16 → UInt8) :
    imClrBytes 0 0xFF (imStx 0 ram) = imClrPages 0 ram := by
  funext i
  generalize hr : ram i = r
  simp only [imClrBytes, imStx, imClrPages, hr]
  bv_decide (config := { enums := false })

theorem imClrPages_succ (x : UInt8) (hx : x ≤ 7) (h0 : x ≠ 0) (ram : UInt16 → UInt8) :
    imClrPages (x - 1) (imClrBytes x 0xFF (imStx x ram)) = imClrPages x ram := by
  funext i
  generalize hr : ram i = r
  simp only [imClrBytes, imStx, imClrPages, hr]
  bv_decide (config := { enums := false })

theorem imStx_6 (x : UInt8) (ram : UInt16 → UInt8) (h6 : ram 6 = 0) : imStx x ram 6 = 0 := by
  simp only [imStx, h6]
  bv_decide (config := { enums := false })

theorem imStx_7 (x : UInt8) (ram : UInt16 → UInt8) : imStx x ram 7 = x := by
  simp only [imStx]
  bv_decide (config := { enums := false })

theorem imClrBytes_6 (x y : UInt8) (ram : UInt16 → UInt8) (h6 : ram 6 = 0) : imClrBytes x y ram 6 = 0 := by
  simp only [imClrBytes, h6]
  bv_decide (config := { enums := false })

/-- The page loop with `Y = $FF`, by induction on `x`. -/
theorem imPages (stop : UInt16) (hstop : ∀ a : UInt16, (0x90D2 ≤ a && a ≤ 0x90E5) = true → a ≠ stop)
    (sp : UInt8) (prg : UInt16 → UInt8) (bad : Bool)
    (hcode : CodeAt prg 0x10CC initMemCode) (n : Nat) :
    ∀ (m : Nat) (x p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64), x.toNat = n → x ≤ 7 →
    (p &&& 4 == 0) = false → ram 6 = 0 →
    ∃ j p' c', ((CPU.runTo (σ := Plain) stop (m + 2051 * (n + 1))).run ⟨⟨0x90D2, 0, x, 0xFF, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0x90E6, 0, 0xFF, 0xFF, sp, p'⟩, imClrPages x ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  have hsS : ∀ a : UInt16, (0x90D2 ≤ a && a ≤ 0x90D3) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have hsB : ∀ a : UInt16, (0x90D4 ≤ a && a ≤ 0x90E2) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have hsT : ∀ a : UInt16, (0x90E3 ≤ a && a ≤ 0x90E5) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have hyF : (0xFF : UInt8).toNat = 255 := by decide
  induction n with
  | zero =>
    intro m x p ram cyc hn hx hI h6
    have hx0 : x = 0 := by
      apply UInt8.toNat_inj.mp; simpa using hn
    subst hx0
    obtain ⟨j1, p1, c1, h1, hI1⟩ := imStxRun stop hsS (m + 2 + 8 * (255 + 1)) 0 0xFF sp p ram prg cyc bad hcode hI
    obtain ⟨j2, p2, c2, h2, hI2⟩ := imBytes stop hsB 0 sp prg bad hcode (by decide) 255 (j1 + m + 2) 0xFF p1 (imStx 0 ram) c1 hyF hI1
      (imStx_6 0 ram h6) (imStx_7 0 ram)
    obtain ⟨j3, p3, c3, h3, hI3⟩ := imTail stop hsT (j2 + (j1 + m)) 0 0xFF sp p2 (imClrBytes 0 0xFF (imStx 0 ram)) prg c2 bad hcode hI2 (by decide)
    refine ⟨j3 + (j2 + j1), p3, c3, ?_, hI3⟩
    have e1 : m + 2051 * (0 + 1) = m + 2 + 8 * (255 + 1) + 1 := by omega
    have e2 : j1 + (m + 2 + 8 * (255 + 1)) = j1 + m + 2 + 8 * (255 + 1) := by simp only [Nat.add_assoc]
    have e3 : j2 + (j1 + m + 2) = j2 + (j1 + m) + 2 := by omega
    have e4 : j3 + (j2 + j1) + m = j3 + (j2 + (j1 + m)) := by omega
    rw [e1, h1, e2, h2, e3, h3, e4, imClrPages_zero]
    rfl
  | succ n ih =>
    intro m x p ram cyc hn hx hI h6
    obtain ⟨hn', hx0⟩ := toNat_pred x n hn
    have hx' : x - 1 ≤ 7 := by revert hx hx0; bv_decide (config := { enums := false })
    obtain ⟨j1, p1, c1, h1, hI1⟩ := imStxRun stop hsS (m + 2051 * (n + 1) + 2 + 8 * (255 + 1)) x 0xFF sp p ram prg cyc bad hcode hI
    obtain ⟨j2, p2, c2, h2, hI2⟩ := imBytes stop hsB x sp prg bad hcode hx 255 (j1 + m + 2051 * (n + 1) + 2) 0xFF p1 (imStx x ram) c1 hyF hI1
      (imStx_6 x ram h6) (imStx_7 x ram)
    obtain ⟨j3, p3, c3, h3, hI3⟩ := imTail stop hsT (j2 + (j1 + m + 2051 * (n + 1))) x 0xFF sp p2 (imClrBytes x 0xFF (imStx x ram)) prg c2 bad hcode hI2 hx
    obtain ⟨j4, p4, c4, h4, hI4⟩ := ih (j3 + (j2 + (j1 + m))) (x - 1) p3 (imClrBytes x 0xFF (imStx x ram)) c3 hn' hx' hI3
      (imClrBytes_6 x 0xFF _ (imStx_6 x ram h6))
    refine ⟨j4 + (j3 + (j2 + j1)), p4, c4, ?_, hI4⟩
    have hb : (x == 0) = false := by simpa using hx0
    have e1 : m + 2051 * (n + 1 + 1) = m + 2051 * (n + 1) + 2 + 8 * (255 + 1) + 1 := by omega
    have e2 : j1 + (m + 2051 * (n + 1) + 2 + 8 * (255 + 1)) = j1 + m + 2051 * (n + 1) + 2 + 8 * (255 + 1) := by simp only [Nat.add_assoc]
    have e3 : j2 + (j1 + m + 2051 * (n + 1) + 2) = j2 + (j1 + m + 2051 * (n + 1)) + 2 := by simp only [Nat.add_assoc]
    have e4 : j3 + (j2 + (j1 + m + 2051 * (n + 1))) = j3 + (j2 + (j1 + m)) + 2051 * (n + 1) := by simp only [Nat.add_assoc]
    have e5 : j4 + (j3 + (j2 + j1)) + m = j4 + (j3 + (j2 + (j1 + m))) := by omega
    rw [e1, h1, e2, h2, e3, h3, hb, Bool.cond_false, e4, h4, e5, imClrPages_succ x hx hx0]

/-- The closed form of `InitializeMemory` entered with `Y = y`: `$0000-$06FF` and `$0700-$07yy` become 0,
except the reserved stack range `$0160-$01FF`. Everything else, `$0800` and up included (never addressed), is kept. -/
def initMemRam (y : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  bif (i >>> 8 < 7 || i >>> 8 == 7 && i &&& 0xFF ≤ y.toUInt16) && !(i >>> 8 == 1 && 0x60 ≤ i &&& 0xFF) then 0 else ram i

/-- `$06 := 0`. -/
def imSta6 (ram : UInt16 → UInt8) (i : UInt16) : UInt8 := bif i == 6 then 0 else ram i

set_option maxHeartbeats 4000000 in
/-- `$90CC`: `ldx #7`, `lda #0`, `sta $06`. -/
theorem imHead (stop : UInt16) (hstop : ∀ a : UInt16, (0x90CC ≤ a && a ≤ 0x90D1) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x10CC initMemCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j p' c', ((CPU.runTo (σ := Plain) stop (m + 3)).run ⟨⟨0x90CC, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0x90D2, 0, 7, y, sp, p'⟩, imSta6 ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, initMemCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3)).run ⟨⟨0x90CC, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI] until 0x90D2
  all_goals
    intros
    subst hrun
    subst_vars
    call_finish [imSta6]

theorem initMemRam_compose (y : UInt8) (ram : UInt16 → UInt8) :
    imClrPages 6 (imClrBytes 7 y (imStx 7 (imSta6 ram))) = initMemRam y ram := by
  funext i
  generalize hr : ram i = r
  simp only [imClrBytes, imStx, imClrPages, imSta6, initMemRam, hr]
  bv_decide (config := { enums := false })

/-- **`InitializeMemory`.** From `$90CC` with any registers to its `rts` at `$90E6`: exactly `initMemRam`. -/
theorem initMem_call (stop : UInt16) (hstop : ∀ a : UInt16, (0x90CC ≤ a && a ≤ 0x90E5) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x10CC initMemCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j p' c', ((CPU.runTo (σ := Plain) stop (m + 16411)).run ⟨⟨0x90CC, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0x90E6, 0, 0xFF, 0xFF, sp, p'⟩, initMemRam y ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  have hsH : ∀ a : UInt16, (0x90CC ≤ a && a ≤ 0x90D1) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have hsS : ∀ a : UInt16, (0x90D2 ≤ a && a ≤ 0x90D3) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have hsB : ∀ a : UInt16, (0x90D4 ≤ a && a ≤ 0x90E2) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have hsT : ∀ a : UInt16, (0x90E3 ≤ a && a ≤ 0x90E5) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  have hsP : ∀ a : UInt16, (0x90D2 ≤ a && a ≤ 0x90E5) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide (config := { enums := false })
  let R1 := imSta6 ram
  let R2 := imStx 7 R1
  have h61 : R1 6 = 0 := by
    simp only [R1, imSta6]; bv_decide (config := { enums := false })
  obtain ⟨j0, p0, c0, h0, hI0⟩ := imHead stop hsH (m + 2051 * (6 + 1) + 2 + 8 * (y.toNat + 1) + (2048 - 8 * (y.toNat + 1)) + 1) a x y sp p ram prg cyc bad hcode hI
  obtain ⟨j1, p1, c1, h1, hI1⟩ := imStxRun stop hsS (j0 + (m + 2051 * (6 + 1) + 2 + 8 * (y.toNat + 1) + (2048 - 8 * (y.toNat + 1)))) 7 y sp p0 R1 prg c0 bad hcode hI0
  obtain ⟨j2, p2, c2, h2, hI2⟩ := imBytes stop hsB 7 sp prg bad hcode (by decide) y.toNat (j1 + (j0 + (m + 2051 * (6 + 1) + 2)) + (2048 - 8 * (y.toNat + 1))) y p1 R2 c1 rfl hI1
    (imStx_6 7 R1 h61) (imStx_7 7 R1)
  obtain ⟨j3, p3, c3, h3, hI3⟩ := imTail stop hsT (j2 + (j1 + (j0 + (m + 2051 * (6 + 1)))) + (2048 - 8 * (y.toNat + 1))) 7 0xFF sp p2 (imClrBytes 7 y R2) prg c2 bad hcode hI2 (by decide)
  have h64 : imClrBytes 7 y R2 6 = 0 := imClrBytes_6 7 y _ (imStx_6 7 R1 h61)
  obtain ⟨j4, p4, c4, h4, hI4⟩ := imPages stop hsP sp prg bad hcode 6 (j3 + (j2 + (j1 + (j0 + m))) + (2048 - 8 * (y.toNat + 1))) 6 p3 (imClrBytes 7 y R2) c3 (by decide) (by decide) hI3 h64
  have hyb : y.toNat ≤ 255 := by
    have := y.toNat_lt; omega
  refine ⟨j4 + (j3 + (j2 + (j1 + j0))) + (2048 - 8 * (y.toNat + 1)), p4, c4, ?_, hI4⟩
  have e0 : m + 16411 = m + 2051 * (6 + 1) + 2 + 8 * (y.toNat + 1) + (2048 - 8 * (y.toNat + 1)) + 1 + 3 := by omega
  have e1 : j0 + (m + 2051 * (6 + 1) + 2 + 8 * (y.toNat + 1) + (2048 - 8 * (y.toNat + 1)) + 1) =
      j0 + (m + 2051 * (6 + 1) + 2 + 8 * (y.toNat + 1) + (2048 - 8 * (y.toNat + 1))) + 1 := by omega
  have e2 : j1 + (j0 + (m + 2051 * (6 + 1) + 2 + 8 * (y.toNat + 1) + (2048 - 8 * (y.toNat + 1)))) =
      j1 + (j0 + (m + 2051 * (6 + 1) + 2)) + (2048 - 8 * (y.toNat + 1)) + 8 * (y.toNat + 1) := by omega
  have e3 : j2 + (j1 + (j0 + (m + 2051 * (6 + 1) + 2)) + (2048 - 8 * (y.toNat + 1))) =
      j2 + (j1 + (j0 + (m + 2051 * (6 + 1)))) + (2048 - 8 * (y.toNat + 1)) + 2 := by omega
  have e4 : j3 + (j2 + (j1 + (j0 + (m + 2051 * (6 + 1)))) + (2048 - 8 * (y.toNat + 1))) =
      j3 + (j2 + (j1 + (j0 + m))) + (2048 - 8 * (y.toNat + 1)) + 2051 * (6 + 1) := by omega
  have e5 : j4 + (j3 + (j2 + (j1 + j0))) + (2048 - 8 * (y.toNat + 1)) + m =
      j4 + (j3 + (j2 + (j1 + (j0 + m))) + (2048 - 8 * (y.toNat + 1))) := by omega
  have hc : ((7 : UInt8) == 0) = false := by decide
  rw [e0, h0, e1, h1, e2, h2, e3, h3, hc, Bool.cond_false]
  have hs : (7 : UInt8) - 1 = 6 := by decide
  rw [hs, e4, h4, e5]
  have hr : imClrPages 6 (imClrBytes 7 y R2) = initMemRam y ram := initMemRam_compose y ram
  rw [hr]

end Smb.Routine
