import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
The actual sprite-offset initialization load and store cannot create the finish
predicate, even for an arbitrary index. Only three source/destination pairs need
ROM facts. The NES transfer retains Quiet and makes no PPU-support or caller-
history claim; this stops before DEX and does not prove the whole loop.
-/

namespace Smb.Routine.SpriteInitFinish
open Smb.Routine

def finish (s : Plain) : Bool :=
  s.ram 0x770 == 2 && s.ram 0x75f == 7 && s.ram 0x75c == 3

/- Actual LDA $8FBC,X; STA $06E4,X. Stop before DEX at $90B1. -/
def spriteCode : List UInt8 := smbPrg% 0x90AB 6

def Post (x y sp : UInt8) (ram prg : UInt16 → UInt8) (t : Plain) : Prop :=
  t.bad = false ∧ t.regs.pc = 0x90b1 ∧
  t.regs.x = x ∧ t.regs.y = y ∧ t.regs.s = sp ∧ t.prg = prg ∧
  (finish t = true → (ram 0x770 == 2 && ram 0x75f == 7 && ram 0x75c == 3) = true)

/- The three data premises are actual ROM bytes at the only possible finish aliases.
No bound on X, named-table domain, or initial accumulator value is assumed. -/
set_option maxHeartbeats 4000000 in
theorem sprite_init_cut (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x10ab spriteCode) (hp : p &&& 4 ≠ 0)
    (hlevel : prg 0x1034 = 7) (hworld : prg 0x1037 = 0xad)
    (hmode : prg 0x1048 = 0xcc) :
    Post x y sp ram prg ((CPU.runTo (σ := Plain) 0x90b1 3).run
      ⟨⟨0x90ab,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 := by
  simp only [CodeAt, spriteCode, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x90b1 3).run
    ⟨⟨0x90ab,a,x,y,sp,p⟩,ram,prg,cyc,false⟩).2 = t
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hr [hc,hI,hlevel,hworld,hmode]
  all_goals
    intros
    clear hc hI
    simp only [Post, finish] at *
    fun_congr
    bv_decide

def actualPrg (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

theorem rom_code : CodeAt actualPrg 0x10ab spriteCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem rom_data : actualPrg 0x1034 = 7 ∧ actualPrg 0x1037 = 0xad ∧
    actualPrg 0x1048 = 0xcc := by native_decide

theorem sprite_init_rom (a x y sp p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hp : p &&& 4 ≠ 0) :
    Post x y sp ram actualPrg ((CPU.runTo (σ := Plain) 0x90b1 3).run
      ⟨⟨0x90ab,a,x,y,sp,p⟩,ram,actualPrg,cyc,false⟩).2 :=
  sprite_init_cut a x y sp p ram actualPrg cyc rom_code hp
    rom_data.1 rom_data.2.1 rom_data.2.2

/-- The actual two-instruction fragment on the NES, under the usual explicit
Quiet entry conditions. An arbitrary X may destroy finish, but cannot create it. -/
theorem sprite_init_nes (s : NES) (hq : s.Quiet) (hrom : s.prg = Smb.prg)
    (hpc : s.pc = 0x90AB) (hI : s.p &&& 4 ≠ 0) :
    let out := ((CPU.runTo (σ := NES) 0x90B1 3).run s).2
    out.pc = 0x90B1 ∧ (finalVictory out = true → finalVictory s = true) ∧ out.Quiet := by
  let out := ((CPU.runTo (σ := NES) 0x90B1 3).run s).2
  let plain := ((CPU.runTo (σ := Plain) 0x90B1 3).run s.toPlain).2
  have hpr : s.toPlain.prg = actualPrg := by
    change (fun a => s.prg.get! (a &&& 0x7FFF).toNat) = actualPrg
    rw [hrom]
    rfl
  have hc : CodeAt s.toPlain.prg 0x10AB spriteCode := by rw [hpr]; exact rom_code
  have hd : s.toPlain.prg 0x1034 = 7 ∧ s.toPlain.prg 0x1037 = 0xAD ∧
      s.toPlain.prg 0x1048 = 0xCC := by rw [hpr]; exact rom_data
  have hp : Post s.x s.y s.s s.toPlain.ram s.toPlain.prg plain := by
    simpa only [plain, NES.toPlain, hpc] using
      sprite_init_cut s.a s.x s.y s.s s.p s.toPlain.ram s.toPlain.prg s.cyc
        hc hI hd.1 hd.2.1 hd.2.2
  have hr := refine_runTo s hq 0x90B1 3 hp.1
  have hm : out.ram.get! 0x770 = plain.ram 0x770 := hr.ram 0x770
  have hw : out.ram.get! 0x75F = plain.ram 0x75F := hr.ram 0x75F
  have hl : out.ram.get! 0x75C = plain.ram 0x75C := hr.ram 0x75C
  have hf : finalVictory out = finish plain := by
    simp only [finalVictory, operMode, finish]
    rw [hm, hw, hl]
  change out.pc = 0x90B1 ∧ (finalVictory out = true → finalVictory s = true) ∧ out.Quiet
  refine ⟨(congrArg Regs.pc hr.regs).trans hp.2.1, ?_,
    ⟨hr.size, hr.ctrl, hr.nmiPending, hr.nmiPolled, hr.dma⟩⟩
  intro h
  rw [hf] at h
  exact hp.2.2.2.2.2.2 h

end Smb.Routine.SpriteInitFinish
