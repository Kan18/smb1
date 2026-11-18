import Smb.Routine.ColumnCopy
import Lean.Elab.Tactic.Omega
/-!
# The column copy cannot create the finish predicate

The actual setup and thirteen iterations, from $94D6 to pre-RTS $9503, cannot
create the three-byte finish predicate in Plain. No column or pointer bound is
assumed; even pointer self-modification is allowed between iterations.

This weaker property needs no RAM-preservation or initial/final bad=false claim.
It therefore does not establish full NES behavior for unsupported accesses, valid
return-stack contents, or supported execution. The preceding ProcessAreaData and
final RTS are excluded. The 337-instruction budget and ordinary induction reuse
ColumnCopy's row arithmetic and code bytes; each local path uses the real filter.
-/

open Smb Smb.Routine Smb.Symbolic
open Smb.Routine.ColumnCopy (copyCode)
namespace Smb.Routine.ColumnFinish
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- Separate unrestricted-column experiment. Plain execution may become bad;
-- no supportedness or pointer preservation is asserted.

def Finish (ram : UInt16 → UInt8) : Prop :=
  ram 0x770 = 2 ∧ ram 0x75F = 7 ∧ ram 0x75C = 3

def IterPost (x y sp : UInt8) (ram prg : UInt16 → UInt8) (t : Plain) : Prop :=
  t.prg = prg ∧ (t.regs.p &&& 4 == 0) = false ∧
  t.regs.pc = (bif x + 1 < 13 then 0x94E0 else 0x9503) ∧
  t.regs.x = x + 1 ∧ t.regs.y = y + 16 ∧ t.regs.s = sp ∧
  (Finish t.ram → Finish ram)

set_option maxHeartbeats 4000000 in
theorem iteration_reach (m : Nat) (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x14D6 copyCode)
    (hI : (p &&& 4 == 0) = false) (hx : x < 13) (hy : y = x * 16) :
    ∃ j t, ((CPU.runTo (σ := Plain) 0x9503 (m + 24)).run
      ⟨⟨0x94E0,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2 =
      ((CPU.runTo 0x9503 (j + m)).run t).2 ∧ IterPost x y sp ram prg t := by
  have htab : prg 0x1504 = 0x10 ∧ prg 0x1505 = 0x51 ∧ prg 0x1506 = 0x88 ∧ prg 0x1507 = 0xC0 := by
    have h := hcode
    simp only [CodeAt, copyCode, UInt16.reduceAdd] at h
    simp [h]
  simp only [CodeAt, copyCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) 0x9503 (m + 24)).run
    ⟨⟨0x94E0,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2 = f
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
    refine ⟨?_, ?_⟩
    · try sym_exec [bne]
      fun_congr
      bv_decide
    · intro hf
      simp only [Finish] at hf ⊢
      try sym_exec [bne] at *
      fun_congr
      bv_decide

def SetupPost (sp : UInt8) (ram prg : UInt16 → UInt8) (t : Plain) : Prop :=
  t.prg = prg ∧ (t.regs.p &&& 4 == 0) = false ∧
  t.regs.pc = 0x94E0 ∧ t.regs.x = 0 ∧ t.regs.y = 0 ∧ t.regs.s = sp ∧
  (Finish t.ram → Finish ram)

set_option maxHeartbeats 4000000 in
theorem setup_reach (m : Nat) (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x14D6 copyCode)
    (haddr : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) :
    ∃ j t, ((CPU.runTo (σ := Plain) 0x9503 (m + 24)).run
      ⟨⟨0x94D6,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2 =
      ((CPU.runTo 0x9503 (j + m)).run t).2 ∧ SetupPost sp ram prg t := by
  simp only [CodeAt, copyCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, getBlockBufferAddrCode, UInt16.reduceAdd] at haddr
  generalize hrun : ((CPU.runTo (σ := Plain) 0x9503 (m + 24)).run
    ⟨⟨0x94D6,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2 = f
  sym_run hrun [hcode, haddr, hI] until 38112
  all_goals
    intros
    clear hcode haddr
    subst hrun
    call_fuel
    refine ⟨_, rfl, ?_⟩
    simp only [SetupPost, ← and_assoc]
    refine ⟨?_, ?_⟩
    · try sym_exec [bne]
      fun_congr
      bv_decide
    · intro hf
      simp only [Finish] at hf ⊢
      try sym_exec [bne] at *
      fun_congr
      bv_decide

attribute [local irreducible] CPU.runTo

def LoopPost (sp : UInt8) (ram prg : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0x9503 ∧ t.regs.x = 13 ∧ t.regs.y = 208 ∧
  t.regs.s = sp ∧ t.prg = prg ∧ (t.regs.p &&& 4 == 0) = false ∧
  (Finish t.ram → Finish ram)

theorem loop_finish (r : Nat) :
    ∀ (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool),
    x.toNat + r = 13 → y = x * 16 → CodeAt prg 0x14D6 copyCode →
    (p &&& 4 == 0) = false →
    LoopPost sp ram prg ((CPU.runTo (σ := Plain) 0x9503 (m + r * 24 + 1)).run
      ⟨⟨(if r = 0 then 0x9503 else 0x94E0),a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2 := by
  induction r with
  | zero =>
    intro m a x y sp p ram prg cyc bad hrow hy hcode hI
    have hx : x = 13 := UInt8.toNat_inj.mp (by change x.toNat = 13; omega)
    subst x
    change y = 208 at hy
    subst y
    change LoopPost sp ram prg ((CPU.runTo (σ := Plain) 0x9503 (m + 1)).run
      ⟨⟨0x9503,a,13,208,sp,p⟩,ram,prg,cyc,bad⟩).2
    rw [runTo_snd_stop _ 0x9503 m rfl]
    exact ⟨rfl,rfl,rfl,rfl,rfl,hI,fun h => h⟩
  | succ r ih =>
    intro m a x y sp p ram prg cyc bad hrow hy hcode hI
    have hx : x < 13 := UInt8.lt_iff_toNat_lt.mpr (by change x.toNat < 13; omega)
    obtain ⟨hrow',hpcnext⟩ := ColumnCopy.next_row x r hrow
    have hy' : y + 16 = (x + 1) * 16 := by rw [hy]; bv_decide
    obtain ⟨j,t,he,hp⟩ := iteration_reach (m + r * 24 + 1) a x y sp p ram prg cyc bad hcode hI hx hy
    have hfuel : m + (r + 1) * 24 + 1 = (m + r * 24 + 1) + 24 := by omega
    change LoopPost sp ram prg ((CPU.runTo (σ := Plain) 0x9503 (m + (r + 1) * 24 + 1)).run
      ⟨⟨0x94E0,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2
    rw [hfuel, he]
    rcases t with ⟨⟨pc',a',x',y',sp',p'⟩,ram',prg',cyc',bad'⟩
    rcases hp with ⟨hpr,hI',hpc,hx',hyv,hsp,hfinish⟩
    dsimp only at hpr hI' hpc hx' hyv hsp hfinish
    subst prg' pc' x' y' sp'
    rw [hpcnext]
    have hr := ih (j + m) a' (x + 1) (y + 16) sp p' ram' prg cyc' bad'
      hrow' hy' hcode hI'
    simp only [← Nat.add_assoc] at *
    rcases hr with ⟨hrpc,hrx,hry,hrs,hrpr,hrI,hrfinish⟩
    exact ⟨hrpc,hrx,hry,hrs,hrpr,hrI,fun hf => hfinish (hrfinish hf)⟩

-- No column bound and no initial/final bad=false assumption.
theorem copy_bounded (m : Nat) (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x14D6 copyCode)
    (haddr : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) :
    LoopPost sp ram prg ((CPU.runTo (σ := Plain) 0x9503 (m + 337)).run
      ⟨⟨0x94D6,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2 := by
  obtain ⟨j,t,he,hp⟩ := setup_reach (m + 13 * 24 + 1) a x y sp p ram prg cyc bad hcode haddr hI
  have hfuel : m + 337 = (m + 13 * 24 + 1) + 24 := by omega
  rw [hfuel, he]
  rcases t with ⟨⟨pc',a',x',y',sp',p'⟩,ram',prg',cyc',bad'⟩
  rcases hp with ⟨hpr,hI',hpc,hx',hy',hsp,hfinish⟩
  dsimp only at hpr hI' hpc hx' hy' hsp hfinish
  subst prg' pc' x' y' sp'
  have hr := loop_finish 13 (j + m) a' 0 0 sp p' ram' prg cyc' bad'
    (by decide) (by decide) hcode hI'
  simp only [← Nat.add_assoc] at *
  rcases hr with ⟨hrpc,hrx,hry,hrs,hrpr,hrI,hrfinish⟩
  exact ⟨hrpc,hrx,hry,hrs,hrpr,hrI,fun hf => hfinish (hrfinish hf)⟩

theorem cannot_create_finish (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x14D6 copyCode)
    (haddr : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) :
    let t := ((CPU.runTo (σ := Plain) 0x9503 337).run
      ⟨⟨0x94D6,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2
    Finish t.ram → Finish ram := by
  have h := copy_bounded 0 a x y sp p ram prg cyc bad hcode haddr hI
  exact h.2.2.2.2.2.2

end Smb.Routine.ColumnFinish
