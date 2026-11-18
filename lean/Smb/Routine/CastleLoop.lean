import Smb.Data.ProofRom
import Smb.Routine.Common
import Lean.Elab.Tactic.Omega

/-!
CastleObject rendering loop, actual Plain execution from $981B to pre-PLA $9831.
Initial X <= $0A is essential: termination tests equality with $0B, not >=.
Y, scratch $06, other RAM and SP are arbitrary. Only code, I set, initial
bad=false and the X bound are assumed. Includes DEC's dummy old-value write.
This excludes setup calls and the final PLA/RTS. A final corollary transfers
the bounded loop to the full NES CPU/RAM under explicit Quiet and ROM premises.
-/

open Smb Smb.Routine Smb.Symbolic
namespace Smb.Routine.CastleLoop
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- Actual $981B..$9830 bytes. Stop at $9831 BEFORE PLA.
def castleCode : List UInt8 :=
  smbPrg% 0x981B 22

def OutsideLoop (i : UInt16) : Prop := i ≠ 6 ∧ (i < 0x6A1 ∨ 0x6AB < i)

def IterPost (x sp : UInt8) (ram prg : UInt16 → UInt8) (t : Plain) : Prop :=
  t.bad = false ∧ t.prg = prg ∧ (t.regs.p &&& 4 == 0) = false ∧
  t.regs.pc = (bif x + 1 == 11 then 0x9831 else 0x981B) ∧
  t.regs.x = x + 1 ∧ t.regs.s = sp ∧
  (∀ i, OutsideLoop i → t.ram i = ram i)

-- One iteration only: both counter branches and the final BNE.
-- Indexed ROM reads allow arbitrary Y; no table-value premise is needed.
set_option maxHeartbeats 4000000 in
theorem iteration_reach (m : Nat) (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x181B castleCode)
    (hI : (p &&& 4 == 0) = false) (hx : x ≤ 10) :
    ∃ j t, ((CPU.runTo (σ := Plain) 0x9831 (m + 16)).run
      ⟨⟨0x981B,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 =
      ((CPU.runTo 0x9831 (j + m)).run t).2 ∧ IterPost x sp ram prg t := by
  simp only [CodeAt, castleCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) 0x9831 (m + 16)).run
    ⟨⟨0x981B,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = f
  sym_run hrun [hcode, hI] until 38959
  all_goals
    intros
    sym_run hrun [hcode, hI] until [38939, 38961]
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

-- Reuse the single-iteration theorem by ordinary induction on remaining rows.
attribute [local irreducible] CPU.runTo

def LoopPost (sp : UInt8) (ram prg : UInt16 → UInt8) (t : Plain) : Prop :=
  t.bad = false ∧ t.regs.pc = 0x9831 ∧ t.regs.x = 11 ∧
  t.regs.s = sp ∧ t.prg = prg ∧ (t.regs.p &&& 4 == 0) = false ∧
  (∀ i, OutsideLoop i → t.ram i = ram i)

theorem next_row (x : UInt8) (r : Nat) (h : x.toNat + (r + 1) = 11) :
    (x + 1).toNat + r = 11 ∧
    (bif x + 1 == 11 then (0x9831 : UInt16) else 0x981B) =
      (if r = 0 then 0x9831 else 0x981B) := by
  have hn : (x + 1).toNat = x.toNat + 1 := by
    rw [UInt8.toNat_add]
    change (x.toNat + 1) % 256 = x.toNat + 1
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨by omega, ?_⟩
  by_cases hz : r = 0
  · have he : x + 1 = 11 := UInt8.toNat_inj.mp (by change (x + 1).toNat = 11; omega)
    simp [hz, he]
  · have he : x + 1 ≠ 11 := by
      intro he
      have := congrArg UInt8.toNat he
      change (x + 1).toNat = 11 at this
      omega
    simp [hz, he]

theorem loop_finish (r : Nat) :
    ∀ (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64),
    x.toNat + r = 11 → CodeAt prg 0x181B castleCode →
    (p &&& 4 == 0) = false →
    LoopPost sp ram prg ((CPU.runTo (σ := Plain) 0x9831 (m + r * 16 + 1)).run
      ⟨⟨(if r = 0 then 0x9831 else 0x981B),a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  induction r with
  | zero =>
    intro m a x y sp p ram prg cyc hrow hcode hI
    have hx : x = 11 := UInt8.toNat_inj.mp (by change x.toNat = 11; omega)
    subst x
    change LoopPost sp ram prg ((CPU.runTo (σ := Plain) 0x9831 (m + 1)).run
      ⟨⟨0x9831,a,11,y,sp,p⟩,ram,prg,cyc,false⟩).2
    rw [runTo_snd_stop _ 0x9831 m rfl]
    exact ⟨rfl,rfl,rfl,rfl,rfl,hI,fun _ _ => rfl⟩
  | succ r ih =>
    intro m a x y sp p ram prg cyc hrow hcode hI
    have hx : x ≤ 10 := UInt8.le_iff_toNat_le.mpr (by change x.toNat ≤ 10; omega)
    obtain ⟨hrow',hpcnext⟩ := next_row x r hrow
    obtain ⟨j,t,he,hp⟩ := iteration_reach (m + r * 16 + 1) a x y sp p ram prg cyc hcode hI hx
    have hfuel : m + (r + 1) * 16 + 1 = (m + r * 16 + 1) + 16 := by omega
    change LoopPost sp ram prg ((CPU.runTo (σ := Plain) 0x9831 (m + (r + 1) * 16 + 1)).run
      ⟨⟨0x981B,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2
    rw [hfuel, he]
    rcases t with ⟨⟨pc',a',x',y',sp',p'⟩,ram',prg',cyc',bad'⟩
    rcases hp with ⟨hb,hpr,hI',hpc,hx',hsp,hframe⟩
    dsimp only at hb hpr hI' hpc hx' hsp hframe
    subst bad' prg' pc' x' sp'
    rw [hpcnext]
    have hr := ih (j + m) a' (x + 1) y' sp p' ram' prg cyc' hrow' hcode hI'
    simp only [← Nat.add_assoc] at *
    rcases hr with ⟨hrb,hrpc,hrx,hrs,hrpr,hrI,hrframe⟩
    exact ⟨hrb,hrpc,hrx,hrs,hrpr,hrI,fun i hi => (hrframe i hi).trans (hframe i hi)⟩

-- 177 is an instruction-fuel bound, not an exact count or a cycle bound.
theorem castle_bounded (m : Nat) (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x181B castleCode)
    (hI : (p &&& 4 == 0) = false) (hx : x ≤ 10) :
    LoopPost sp ram prg ((CPU.runTo (σ := Plain) 0x9831 (m + 177)).run
      ⟨⟨0x981B,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  have hxn : x.toNat ≤ 10 := UInt8.le_iff_toNat_le.mp hx
  have hr : x.toNat + (11 - x.toNat) = 11 := by omega
  have hn : 11 - x.toNat ≠ 0 := by omega
  have hf : m + x.toNat * 16 + (11 - x.toNat) * 16 + 1 = m + 177 := by omega
  have h := loop_finish (11 - x.toNat) (m + x.toNat * 16) a x y sp p ram prg cyc hr hcode hI
  simpa only [hf, ite_eq_right hn] using h

theorem high_outside (i : UInt16) (hi : 0x700 ≤ i) : OutsideLoop i := by
  simp only [OutsideLoop]
  bv_decide

theorem high_preserved {sp : UInt8} {ram prg : UInt16 → UInt8} {t : Plain}
    (h : LoopPost sp ram prg t) (i : UInt16) (hi : 0x700 ≤ i) : t.ram i = ram i := by
  exact h.2.2.2.2.2.2 i (high_outside i hi)

theorem finish_of_post {sp : UInt8} {ram prg : UInt16 → UInt8} {t : Plain}
    (h : LoopPost sp ram prg t) :
    (t.ram 0x770 = 2 ∧ t.ram 0x75F = 7 ∧ t.ram 0x75C = 3) ↔
      (ram 0x770 = 2 ∧ ram 0x75F = 7 ∧ ram 0x75C = 3) := by
  rw [high_preserved h 0x770 (by decide), high_preserved h 0x75F (by decide),
    high_preserved h 0x75C (by decide)]

-- The complete bounded run preserves the finish predicate in both directions.
theorem castle_finish (m : Nat) (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x181B castleCode)
    (hI : (p &&& 4 == 0) = false) (hx : x ≤ 10) :
    let t := ((CPU.runTo (σ := Plain) 0x9831 (m + 177)).run
      ⟨⟨0x981B,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2
    (t.ram 0x770 = 2 ∧ t.ram 0x75F = 7 ∧ t.ram 0x75C = 3) ↔
      (ram 0x770 = 2 ∧ ram 0x75F = 7 ∧ ram 0x75C = 3) :=
  finish_of_post (castle_bounded m a x y sp p ram prg cyc hcode hI hx)

theorem castle_rom :
    let prg := fun a => Smb.prg.get! (a &&& 0x7FFF).toNat
    CodeAt prg 0x181B castleCode := by
  exact codeAt_of_matches _ _ _ (by native_decide)


/-- Full NES CPU/RAM consequence of the bounded loop. Quiet and the row bound
remain entry assumptions; no PPU-supportedness or whole-caller claim is made. -/
theorem castle_nes_preserves_finish (s : NES) (hq : s.Quiet)
    (hrom : s.prg = Smb.prg) (hpc : s.pc = 0x981B) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false) (hx : s.x ≤ 10) :
    let out := ((CPU.runTo (σ := NES) 0x9831 (m + 177)).run s).2
    out.pc = 0x9831 ∧ out.s = s.s ∧ finalVictory out = finalVictory s ∧ out.Quiet := by
  let out := ((CPU.runTo (σ := NES) 0x9831 (m + 177)).run s).2
  have hc : CodeAt s.toPlain.prg 0x181B castleCode := by
    simpa only [NES.toPlain, hrom] using castle_rom
  have hp : LoopPost s.s s.toPlain.ram s.toPlain.prg
      ((CPU.runTo (σ := Plain) 0x9831 (m + 177)).run s.toPlain).2 := by
    simpa only [NES.toPlain, hpc] using
      castle_bounded m s.a s.x s.y s.s s.p s.toPlain.ram s.toPlain.prg s.cyc hc hI hx
  have hr := refine_runTo s hq 0x9831 (m + 177) hp.1
  have hpc' := congrArg Regs.pc hr.regs
  have hsp' := congrArg Regs.s hr.regs
  have hm : out.ram.get! 0x770 = s.ram.get! 0x770 :=
    (hr.ram 0x770).trans (high_preserved hp 0x770 (by decide))
  have hw : out.ram.get! 0x75F = s.ram.get! 0x75F :=
    (hr.ram 0x75F).trans (high_preserved hp 0x75F (by decide))
  have hl : out.ram.get! 0x75C = s.ram.get! 0x75C :=
    (hr.ram 0x75C).trans (high_preserved hp 0x75C (by decide))
  dsimp only at hpc' hsp'
  change out.pc = 0x9831 ∧ out.s = s.s ∧ finalVictory out = finalVictory s ∧ out.Quiet
  refine ⟨hpc'.trans hp.2.1, hsp'.trans hp.2.2.2.1, ?_, ?_⟩
  · simp only [finalVictory, operMode]
    rw [hm, hw, hl]
  · exact ⟨hr.size, hr.ctrl, hr.nmiPending, hr.nmiPolled, hr.dma⟩

end Smb.Routine.CastleLoop
