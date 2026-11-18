import Smb.Data.ProofRom
import Smb.Routine.BlockBuffer
import Lean.Elab.Tactic.Omega

/-!
# The normal block-buffer column copy

The actual run from $94D6, after ProcessAreaData, through all thirteen rows ends
before RTS at $9503. One iteration is checked once and composed by induction.
Entry column <32, code bytes, I set and Plain support remain explicit premises.

The endpoint preserves every RAM value outside the two buffers, scratch $00/$06/$07
and three wrapping stack cells. In particular the column, area selectors and finish
bytes are preserved. This is not a proof of parser history or full NES supportedness.
Fuel 337 counts instructions, not cycles, video frames or an exact execution length.
-/

open Smb Smb.Routine Smb.Symbolic
namespace Smb.Routine.ColumnCopy
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- Entry is AFTER ProcessAreaData. Includes the final RTS and four threshold bytes.
def copyCode : List UInt8 := smbPrg% 0x94D6 50
def stackCell (sp : UInt8) : UInt16 := (0x100 ||| sp.toUInt16) &&& 0x7FF

def OutsideLoop (i : UInt16) : Prop := i ≠ 0 ∧ (i < 0x500 ∨ 0x69F < i)
def OutsideCopy (sp : UInt8) (i : UInt16) : Prop :=
  OutsideLoop i ∧ i ≠ 6 ∧ i ≠ 7 ∧ i ≠ stackCell sp ∧
    i ≠ stackCell (sp + 255) ∧ i ≠ stackCell (sp + 254)

def IterPost (x y sp : UInt8) (ram prg : UInt16 → UInt8) (t : Plain) : Prop :=
  t.bad = false ∧ t.prg = prg ∧ (t.regs.p &&& 4 == 0) = false ∧
  t.regs.pc = (bif x + 1 < 13 then 0x94E0 else 0x9503) ∧
  t.regs.x = x + 1 ∧ t.regs.y = y + 16 ∧ t.regs.s = sp ∧
  t.ram 6 = ram 6 ∧ t.ram 7 = ram 7 ∧
  (∀ i, OutsideLoop i → t.ram i = ram i)

-- One actual iteration, including BCC, expressed as a continuation equality.
-- No expansion of other iterations occurs here.
set_option maxHeartbeats 4000000 in
theorem iteration_reach (m : Nat) (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x14D6 copyCode)
    (hI : (p &&& 4 == 0) = false) (hx : x < 13) (hy : y = x * 16)
    (hlo : ram 6 ≤ 0xDF) (hhi : ram 7 = 5) :
    ∃ j t, ((CPU.runTo (σ := Plain) 0x9503 (m + 24)).run
      ⟨⟨0x94E0,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 =
      ((CPU.runTo 0x9503 (j + m)).run t).2 ∧ IterPost x y sp ram prg t := by
  simp only [CodeAt, copyCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) 0x9503 (m + 24)).run
    ⟨⟨0x94E0,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = f
  sym_run hrun [hcode, hI] until 38145
  all_goals
    intros
    sym_run hrun [hcode, hI] until [38112, 38147]
  all_goals
    intros
    clear hcode
    subst hrun
    call_fuel
    refine ⟨_, rfl, ?_⟩
    simp only [IterPost, ← and_assoc]
    refine ⟨?_, fun i hi => ?_⟩
    · sym_exec [bne]
      fun_congr
      bv_decide
    · simp only [OutsideLoop] at hi
      try sym_exec [bne]
      fun_congr
      bv_decide

def SetupPost (sp : UInt8) (ram prg : UInt16 → UInt8) (t : Plain) : Prop :=
  t.bad = false ∧ t.prg = prg ∧ (t.regs.p &&& 4 == 0) = false ∧
  t.regs.pc = 0x94E0 ∧ t.regs.x = 0 ∧ t.regs.y = 0 ∧ t.regs.s = sp ∧
  t.ram 6 ≤ 0xDF ∧ t.ram 7 = 5 ∧
  (∀ i, OutsideCopy sp i → t.ram i = ram i)

set_option maxHeartbeats 4000000 in
theorem setup_reach (m : Nat) (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x14D6 copyCode)
    (haddr : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) (hcol : ram 0x6A0 < 32) :
    ∃ j t, ((CPU.runTo (σ := Plain) 0x9503 (m + 24)).run
      ⟨⟨0x94D6,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 =
      ((CPU.runTo 0x9503 (j + m)).run t).2 ∧ SetupPost sp ram prg t := by
  have htab : prg 0x1BDD = 0 ∧ prg 0x1BDE = 0xD0 ∧ prg 0x1BDF = 5 ∧ prg 0x1BE0 = 5 := by
    have h := haddr
    simp only [CodeAt, getBlockBufferAddrCode, UInt16.reduceAdd] at h
    simp [h]
  simp only [CodeAt, copyCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, getBlockBufferAddrCode, UInt16.reduceAdd] at haddr
  generalize hrun : ((CPU.runTo (σ := Plain) 0x9503 (m + 24)).run
    ⟨⟨0x94D6,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = f
  sym_run hrun [hcode, haddr, hI] until 38112
  all_goals
    intros
    clear hcode haddr
    subst hrun
    call_fuel
    refine ⟨_, rfl, ?_⟩
    simp only [SetupPost, ← and_assoc]
    refine ⟨?_, fun i hi => ?_⟩
    · sym_exec [bne]
      fun_congr
      bv_decide
    · simp only [OutsideCopy, OutsideLoop, stackCell] at hi
      try sym_exec [bne]
      fun_congr
      bv_decide

-- Composition is ordinary induction over the remaining rows. The interpreter
-- is kept opaque; each induction step reuses the proved iteration once.
attribute [local irreducible] CPU.runTo

def LoopPost (sp : UInt8) (ram prg : UInt16 → UInt8) (t : Plain) : Prop :=
  t.bad = false ∧ t.regs.pc = 0x9503 ∧ t.regs.x = 13 ∧ t.regs.y = 208 ∧
  t.regs.s = sp ∧ t.prg = prg ∧ (t.regs.p &&& 4 == 0) = false ∧
  (∀ i, OutsideLoop i → t.ram i = ram i)

theorem next_row (x : UInt8) (r : Nat) (h : x.toNat + (r + 1) = 13) :
    (x + 1).toNat + r = 13 ∧
    (bif x + 1 < 13 then (0x94E0 : UInt16) else 0x9503) =
      (if r = 0 then 0x9503 else 0x94E0) := by
  have hx : x.toNat < 13 := by omega
  have hn : (x + 1).toNat = x.toNat + 1 := by
    rw [UInt8.toNat_add]
    change (x.toNat + 1) % 256 = x.toNat + 1
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨by omega, ?_⟩
  by_cases hz : r = 0
  · have he : x + 1 = 13 := UInt8.toNat_inj.mp (by change (x + 1).toNat = 13; omega)
    simp [hz, he]
  · have hl : x + 1 < 13 := UInt8.lt_iff_toNat_lt.mpr (by change (x + 1).toNat < 13; omega)
    simp [hz, hl]

theorem loop_finish (r : Nat) :
    ∀ (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64),
    x.toNat + r = 13 → y = x * 16 → CodeAt prg 0x14D6 copyCode →
    (p &&& 4 == 0) = false → ram 6 ≤ 0xDF → ram 7 = 5 →
    LoopPost sp ram prg ((CPU.runTo (σ := Plain) 0x9503 (m + r * 24 + 1)).run
      ⟨⟨(if r = 0 then 0x9503 else 0x94E0),a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  induction r with
  | zero =>
    intro m a x y sp p ram prg cyc hrow hy hcode hI hlo hhi
    have hx : x = 13 := UInt8.toNat_inj.mp (by change x.toNat = 13; omega)
    subst x
    change y = 208 at hy
    subst y
    change LoopPost sp ram prg ((CPU.runTo (σ := Plain) 0x9503 (m + 1)).run
      ⟨⟨0x9503,a,13,208,sp,p⟩,ram,prg,cyc,false⟩).2
    rw [runTo_snd_stop _ 0x9503 m rfl]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,hI,fun _ _ => rfl⟩
  | succ r ih =>
    intro m a x y sp p ram prg cyc hrow hy hcode hI hlo hhi
    have hx : x < 13 := UInt8.lt_iff_toNat_lt.mpr (by change x.toNat < 13; omega)
    obtain ⟨hrow',hpcnext⟩ := next_row x r hrow
    have hy' : y + 16 = (x + 1) * 16 := by rw [hy]; bv_decide
    obtain ⟨j,t,he,hp⟩ := iteration_reach (m + r * 24 + 1) a x y sp p ram prg cyc hcode hI hx hy hlo hhi
    have hfuel : m + (r + 1) * 24 + 1 = (m + r * 24 + 1) + 24 := by omega
    change LoopPost sp ram prg ((CPU.runTo (σ := Plain) 0x9503 (m + (r + 1) * 24 + 1)).run
      ⟨⟨0x94E0,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2
    rw [hfuel, he]
    rcases t with ⟨⟨pc',a',x',y',sp',p'⟩,ram',prg',cyc',bad'⟩
    rcases hp with ⟨hb,hpr,hI',hpc,hx',hyv,hsp,hlo',hhi',hframe⟩
    dsimp only at hb hpr hI' hpc hx' hyv hsp hlo' hhi' hframe
    subst bad' prg' pc' x' y' sp'
    rw [hpcnext]
    have hr := ih (j + m) a' (x + 1) (y + 16) sp p' ram' prg cyc'
      hrow' hy' hcode hI' (hlo' ▸ hlo) (hhi' ▸ hhi)
    simp only [← Nat.add_assoc] at *
    rcases hr with ⟨hrb,hrpc,hrx,hry,hrs,hrpr,hrI,hrframe⟩
    exact ⟨hrb,hrpc,hrx,hry,hrs,hrpr,hrI,fun i hi => (hrframe i hi).trans (hframe i hi)⟩

def CopyPost (sp : UInt8) (ram prg : UInt16 → UInt8) (t : Plain) : Prop :=
  t.bad = false ∧ t.regs.pc = 0x9503 ∧ t.regs.x = 13 ∧ t.regs.y = 208 ∧
  t.regs.s = sp ∧ t.prg = prg ∧ (t.regs.p &&& 4 == 0) = false ∧
  (∀ i, OutsideCopy sp i → t.ram i = ram i)

theorem copy_bounded (m : Nat) (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x14D6 copyCode)
    (haddr : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) (hcol : ram 0x6A0 < 32) :
    CopyPost sp ram prg ((CPU.runTo (σ := Plain) 0x9503 (m + 337)).run
      ⟨⟨0x94D6,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  obtain ⟨j,t,he,hp⟩ := setup_reach (m + 13 * 24 + 1) a x y sp p ram prg cyc hcode haddr hI hcol
  have hfuel : m + 337 = (m + 13 * 24 + 1) + 24 := by omega
  rw [hfuel, he]
  rcases t with ⟨⟨pc',a',x',y',sp',p'⟩,ram',prg',cyc',bad'⟩
  rcases hp with ⟨hb,hpr,hI',hpc,hx',hy',hsp,hlo,hhi,hframe⟩
  dsimp only at hb hpr hI' hpc hx' hy' hsp hlo hhi hframe
  subst bad' prg' pc' x' y' sp'
  have hr := loop_finish 13 (j + m) a' 0 0 sp p' ram' prg cyc'
    (by decide) (by decide) hcode hI' hlo hhi
  simp only [← Nat.add_assoc] at *
  rcases hr with ⟨hrb,hrpc,hrx,hry,hrs,hrpr,hrI,hrframe⟩
  exact ⟨hrb,hrpc,hrx,hry,hrs,hrpr,hrI,fun i hi => (hrframe i hi.1).trans (hframe i hi)⟩

theorem copy_rom :
    let prg := fun a => Smb.prg.get! (a &&& 0x7FFF).toNat
    CodeAt prg 0x14D6 copyCode ∧ CodeAt prg 0x1BDD getBlockBufferAddrCode := by
  exact ⟨codeAt_of_matches _ _ _ (by native_decide), codeAt_of_matches _ _ _ (by native_decide)⟩

-- Every selector/finish byte is above the possible copy writes and stack page.
theorem high_outside (sp : UInt8) (i : UInt16) (hi : 0x700 ≤ i) : OutsideCopy sp i := by
  simp only [OutsideCopy, OutsideLoop, stackCell]
  bv_decide

def SelectorsPreserved (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.ram 0x750 = ram 0x750 ∧ t.ram 0x751 = ram 0x751 ∧
  t.ram 0x75C = ram 0x75C ∧ t.ram 0x75F = ram 0x75F ∧ t.ram 0x770 = ram 0x770

theorem selectors_of_post {sp : UInt8} {ram prg : UInt16 → UInt8} {t : Plain}
    (h : CopyPost sp ram prg t) : SelectorsPreserved ram t := by
  rcases h with ⟨_,_,_,_,_,_,_,hf⟩
  exact ⟨hf _ (high_outside sp _ (by decide)), hf _ (high_outside sp _ (by decide)),
    hf _ (high_outside sp _ (by decide)), hf _ (high_outside sp _ (by decide)),
    hf _ (high_outside sp _ (by decide))⟩

theorem copy_selectors (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x14D6 copyCode)
    (haddr : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) (hcol : ram 0x6A0 < 32) :
    SelectorsPreserved ram ((CPU.runTo (σ := Plain) 0x9503 337).run
      ⟨⟨0x94D6,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 :=
  selectors_of_post (copy_bounded 0 a x y sp p ram prg cyc hcode haddr hI hcol)

theorem finish_of_post {sp : UInt8} {ram prg : UInt16 → UInt8} {t : Plain}
    (h : CopyPost sp ram prg t) :
    (t.ram 0x770 = 2 ∧ t.ram 0x75F = 7 ∧ t.ram 0x75C = 3) ↔
      (ram 0x770 = 2 ∧ ram 0x75F = 7 ∧ ram 0x75C = 3) := by
  rcases selectors_of_post h with ⟨_,_,hl,hw,hm⟩
  rw [hl,hw,hm]

theorem column_outside (sp : UInt8) : OutsideCopy sp 0x6A0 := by
  simp only [OutsideCopy, OutsideLoop, stackCell]
  bv_decide

theorem column_preserved {sp : UInt8} {ram prg : UInt16 → UInt8} {t : Plain}
    (h : CopyPost sp ram prg t) : t.ram 0x6A0 = ram 0x6A0 := by
  rcases h with ⟨_,_,_,_,_,_,_,hf⟩
  exact hf _ (column_outside sp)

theorem column_bound {sp : UInt8} {ram prg : UInt16 → UInt8} {t : Plain}
    (h : CopyPost sp ram prg t) (hc : ram 0x6A0 < 32) : t.ram 0x6A0 < 32 := by
  rw [column_preserved h]
  exact hc

end Smb.Routine.ColumnCopy
