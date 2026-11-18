import Smb.Data.ProofRom
import Smb.Routine.Common

namespace Smb.Routine.LiteralIndexedFinish
open Smb.Routine

/- Fifteen local LDA-immediate/STA-absolute-X cuts. Each includes the actual load,
accepts arbitrary A and X, and stops immediately after STA. No loop entry,
back-edge provenance, global reachability, or full-NES result is claimed. -/
def finish (s : Plain) : Bool :=
  s.ram 0x770 == 2 && s.ram 0x75f == 7 && s.ram 0x75c == 3

def Post (stop : UInt16) (value x y sp : UInt8)
    (ram prg : UInt16 → UInt8) (t : Plain) : Prop :=
  t.bad = false ∧ t.regs.pc = stop ∧ t.regs.a = value ∧
  t.regs.x = x ∧ t.regs.y = y ∧ t.regs.s = sp ∧
  t.regs.p &&& 4 ≠ 0 ∧ t.prg = prg ∧
  (finish t = true → (ram 0x770 == 2 && ram 0x75f == 7 && ram 0x75c == 3) = true)

/- $9406 LDA #$00; $9408 STA $06A1,X; stop $940B. -/
def clear_metatilesCode : List UInt8 := smbPrg% 0x9406 5

set_option maxHeartbeats 4000000 in
theorem clear_metatiles (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x1406 clear_metatilesCode) (hp : p &&& 4 ≠ 0) :
    Post 0x940b 0x00 x y sp ram prg ((CPU.runTo (σ := Plain) 0x940b 3).run
      ⟨⟨0x9406,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, clear_metatilesCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x940b 3).run
    ⟨⟨0x9406,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [Post, finish] at *
    fun_congr
    bv_decide

/- $9769 LDA #$17; $976B STA $06A1,X; stop $976E. -/
def tree_middleCode : List UInt8 := smbPrg% 0x9769 5

set_option maxHeartbeats 4000000 in
theorem tree_middle (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x1769 tree_middleCode) (hp : p &&& 4 ≠ 0) :
    Post 0x976e 0x17 x y sp ram prg ((CPU.runTo (σ := Plain) 0x976e 3).run
      ⟨⟨0x9769,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, tree_middleCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x976e 3).run
    ⟨⟨0x9769,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [Post, finish] at *
    fun_congr
    bv_decide

/- $9799 LDA #$1A; $979B STA $06A1,X; stop $979E. -/
def mushroom_topCode : List UInt8 := smbPrg% 0x9799 5

set_option maxHeartbeats 4000000 in
theorem mushroom_top (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x1799 mushroom_topCode) (hp : p &&& 4 ≠ 0) :
    Post 0x979e 0x1a x y sp ram prg ((CPU.runTo (σ := Plain) 0x979e 3).run
      ⟨⟨0x9799,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, mushroom_topCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x979e 3).run
    ⟨⟨0x9799,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [Post, finish] at *
    fun_congr
    bv_decide

/- $97A3 LDA #$4F; $97A5 STA $06A1,X; stop $97A8. -/
def mushroom_stemCode : List UInt8 := smbPrg% 0x97A3 5

set_option maxHeartbeats 4000000 in
theorem mushroom_stem (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x17a3 mushroom_stemCode) (hp : p &&& 4 ≠ 0) :
    Post 0x97a8 0x4f x y sp ram prg ((CPU.runTo (σ := Plain) 0x97a8 3).run
      ⟨⟨0x97a3,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, mushroom_stemCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x97a8 3).run
    ⟨⟨0x97a3,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [Post, finish] at *
    fun_congr
    bv_decide

/- $9877 LDA #$6B; $9879 STA $06A1,X; stop $987C. -/
def water_pipe_topCode : List UInt8 := smbPrg% 0x9877 5

set_option maxHeartbeats 4000000 in
theorem water_pipe_top (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x1877 water_pipe_topCode) (hp : p &&& 4 ≠ 0) :
    Post 0x987c 0x6b x y sp ram prg ((CPU.runTo (σ := Plain) 0x987c 3).run
      ⟨⟨0x9877,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, water_pipe_topCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x987c 3).run
    ⟨⟨0x9877,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [Post, finish] at *
    fun_congr
    bv_decide

/- $987C LDA #$6C; $987E STA $06A2,X; stop $9881. -/
def water_pipe_bottomCode : List UInt8 := smbPrg% 0x987C 5

set_option maxHeartbeats 4000000 in
theorem water_pipe_bottom (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x187c water_pipe_bottomCode) (hp : p &&& 4 ≠ 0) :
    Post 0x9881 0x6c x y sp ram prg ((CPU.runTo (σ := Plain) 0x9881 3).run
      ⟨⟨0x987c,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, water_pipe_bottomCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x9881 3).run
    ⟨⟨0x987c,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [Post, finish] at *
    fun_congr
    bv_decide

/- $9890 LDA #$00; $9892 STA $06A1,X; stop $9895. -/
def intro_pipe_clearCode : List UInt8 := smbPrg% 0x9890 5

set_option maxHeartbeats 4000000 in
theorem intro_pipe_clear (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x1890 intro_pipe_clearCode) (hp : p &&& 4 ≠ 0) :
    Post 0x9895 0x00 x y sp ram prg ((CPU.runTo (σ := Plain) 0x9895 3).run
      ⟨⟨0x9890,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, intro_pipe_clearCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x9895 3).run
    ⟨⟨0x9890,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [Post, finish] at *
    fun_congr
    bv_decide

/- $9973 LDA #$C0; $9975 STA $06A1,X; stop $9978. -/
def question_rowCode : List UInt8 := smbPrg% 0x9973 5

set_option maxHeartbeats 4000000 in
theorem question_row (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x1973 question_rowCode) (hp : p &&& 4 ≠ 0) :
    Post 0x9978 0xc0 x y sp ram prg ((CPU.runTo (σ := Plain) 0x9978 3).run
      ⟨⟨0x9973,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, question_rowCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x9978 3).run
    ⟨⟨0x9973,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [Post, finish] at *
    fun_congr
    bv_decide

/- $9987 LDA #$0B; $9989 STA $06A1,X; stop $998C. -/
def bridgeCode : List UInt8 := smbPrg% 0x9987 5

set_option maxHeartbeats 4000000 in
theorem bridge (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x1987 bridgeCode) (hp : p &&& 4 ≠ 0) :
    Post 0x998c 0x0b x y sp ram prg ((CPU.runTo (σ := Plain) 0x998c 3).run
      ⟨⟨0x9987,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, bridgeCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x998c 3).run
    ⟨⟨0x9987,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [Post, finish] at *
    fun_congr
    bv_decide

/- $9A6E LDA #$64; $9A70 STA $06A1,X; stop $9A73. -/
def cannon_topCode : List UInt8 := smbPrg% 0x9A6E 5

set_option maxHeartbeats 4000000 in
theorem cannon_top (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x1a6e cannon_topCode) (hp : p &&& 4 ≠ 0) :
    Post 0x9a73 0x64 x y sp ram prg ((CPU.runTo (σ := Plain) 0x9a73 3).run
      ⟨⟨0x9a6e,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, cannon_topCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x9a73 3).run
    ⟨⟨0x9a6e,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [Post, finish] at *
    fun_congr
    bv_decide

/- $9A77 LDA #$65; $9A79 STA $06A1,X; stop $9A7C. -/
def cannon_middleCode : List UInt8 := smbPrg% 0x9A77 5

set_option maxHeartbeats 4000000 in
theorem cannon_middle (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x1a77 cannon_middleCode) (hp : p &&& 4 ≠ 0) :
    Post 0x9a7c 0x65 x y sp ram prg ((CPU.runTo (σ := Plain) 0x9a7c 3).run
      ⟨⟨0x9a77,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, cannon_middleCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x9a7c 3).run
    ⟨⟨0x9a77,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [Post, finish] at *
    fun_congr
    bv_decide

/- $9AF6 LDA #$67; $9AF8 STA $06A1,X; stop $9AFB. -/
def spring_topCode : List UInt8 := smbPrg% 0x9AF6 5

set_option maxHeartbeats 4000000 in
theorem spring_top (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x1af6 spring_topCode) (hp : p &&& 4 ≠ 0) :
    Post 0x9afb 0x67 x y sp ram prg ((CPU.runTo (σ := Plain) 0x9afb 3).run
      ⟨⟨0x9af6,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, spring_topCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x9afb 3).run
    ⟨⟨0x9af6,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [Post, finish] at *
    fun_congr
    bv_decide

/- $9AFB LDA #$68; $9AFD STA $06A2,X; stop $9B00. -/
def spring_bottomCode : List UInt8 := smbPrg% 0x9AFB 5

set_option maxHeartbeats 4000000 in
theorem spring_bottom (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x1afb spring_bottomCode) (hp : p &&& 4 ≠ 0) :
    Post 0x9b00 0x68 x y sp ram prg ((CPU.runTo (σ := Plain) 0x9b00 3).run
      ⟨⟨0x9afb,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, spring_bottomCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x9b00 3).run
    ⟨⟨0x9afb,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [Post, finish] at *
    fun_congr
    bv_decide

/- $D7E4 LDA #$01; $D7E6 STA $06BE,X; stop $D7E9. -/
def hammer_collision_setCode : List UInt8 := smbPrg% 0xD7E4 5

set_option maxHeartbeats 4000000 in
theorem hammer_collision_set (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x57e4 hammer_collision_setCode) (hp : p &&& 4 ≠ 0) :
    Post 0xd7e9 0x01 x y sp ram prg ((CPU.runTo (σ := Plain) 0xd7e9 3).run
      ⟨⟨0xd7e4,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, hammer_collision_setCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0xd7e9 3).run
    ⟨⟨0xd7e4,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [Post, finish] at *
    fun_congr
    bv_decide

/- $D7FA LDA #$00; $D7FC STA $06BE,X; stop $D7FF. -/
def hammer_collision_clearCode : List UInt8 := smbPrg% 0xD7FA 5

set_option maxHeartbeats 4000000 in
theorem hammer_collision_clear (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x57fa hammer_collision_clearCode) (hp : p &&& 4 ≠ 0) :
    Post 0xd7ff 0x00 x y sp ram prg ((CPU.runTo (σ := Plain) 0xd7ff 3).run
      ⟨⟨0xd7fa,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, hammer_collision_clearCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0xd7ff 3).run
    ⟨⟨0xd7fa,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI]
  all_goals
    intros
    clear hc hI
    simp only [Post, finish] at *
    fun_congr
    bv_decide

def actualPrg (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

/- Actual-ROM identities discharge every cut's code premise. -/
theorem rom_clear_metatiles : CodeAt actualPrg 0x1406 clear_metatilesCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_tree_middle : CodeAt actualPrg 0x1769 tree_middleCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_mushroom_top : CodeAt actualPrg 0x1799 mushroom_topCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_mushroom_stem : CodeAt actualPrg 0x17a3 mushroom_stemCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_water_pipe_top : CodeAt actualPrg 0x1877 water_pipe_topCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_water_pipe_bottom : CodeAt actualPrg 0x187c water_pipe_bottomCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_intro_pipe_clear : CodeAt actualPrg 0x1890 intro_pipe_clearCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_question_row : CodeAt actualPrg 0x1973 question_rowCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_bridge : CodeAt actualPrg 0x1987 bridgeCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_cannon_top : CodeAt actualPrg 0x1a6e cannon_topCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_cannon_middle : CodeAt actualPrg 0x1a77 cannon_middleCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_spring_top : CodeAt actualPrg 0x1af6 spring_topCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_spring_bottom : CodeAt actualPrg 0x1afb spring_bottomCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_hammer_collision_set : CodeAt actualPrg 0x57e4 hammer_collision_setCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_hammer_collision_clear : CodeAt actualPrg 0x57fa hammer_collision_clearCode :=
  codeAt_of_matches _ _ _ (by native_decide)

end Smb.Routine.LiteralIndexedFinish
