import Smb.Data.ProofRom
import Smb.Routine.Firebar

/-!
# Slot independence: small facts about what a new enemy gets from the slot's previous occupant

These results apply to the named code ranges on the plain machine. Reachability of the entry states
is a separate obligation.
-/
namespace Smb.Routine

set_option linter.unusedVariables false

/-! ## 1. The flagpole flag's descent depends on the slot's old `YMF_Dummy`

`FlagpoleRoutine`, `$B86B`–`$B884`, with the flag in slot 5:
```
lda Enemy_Y_Position,x / cmp #$aa / bcs GiveFPScr
lda Player_Y_Position  / cmp #$a2 / bcs GiveFPScr     ; both not taken: carry clear
lda Enemy_YMF_Dummy,x  / adc #$ff / sta Enemy_YMF_Dummy,x
lda Enemy_Y_Position,x / adc #$01 / sta Enemy_Y_Position,x
```
`adc #$ff` is "minus 1, carry set unless the byte was 0". So the flag moves 2 pixels a frame, except 1
on the frame the dummy byte is 0. `FlagpoleObject` sets the flag's position only, so that byte is whatever
slot 5 held: 0 on a fresh area (a 1-pixel step on the first frame), or a power-up's leftover. -/

/-- `$B86B`–`$B884`. -/
def flagDescendCode : List UInt8 :=
  smbPrg% 0xB86B 26

def FlagSummary (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xB885 ∧ t.bad = false ∧
  t.ram 0x041C = ram 0x041C - 1 ∧
  t.ram 0x00D4 = ram 0x00D4 + 1 + (if ram 0x041C = 0 then 0 else 1)

set_option maxHeartbeats 40000000 in
theorem flag_step (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xB86B ≤ a && a ≤ 0xB885) = true → a ≠ stop)
    (m : Nat) (a y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x386B flagDescendCode)
    (hI : (p &&& 4 == 0) = false)
    (hflag : ram 0x00D4 < 0xAA) (hplayer : ram 0x00CE < 0xA2) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 16)).run ⟨⟨0xB86B, a, 5, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ FlagSummary ram t := by
  simp only [CodeAt, flagDescendCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 16)).run ⟨⟨0xB86B, a, 5, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hI, hflag, hplayer] until 47237
  all_goals
    intros
    clear hcode
    subst hrun
    reach_finish [FlagSummary]

/-- One frame of descent (the effect `flag_step` proves): dummy byte, flag position. -/
def flagStep (s : UInt8 × UInt8) : UInt8 × UInt8 :=
  (s.1 - 1, s.2 + 1 + (if s.1 = 0 then 0 else 1))

/-- Frames of descent from position `s.2` until the flag reaches `$AA`, the test in `flag_step`. -/
def flagFrames : Nat → UInt8 × UInt8 → Nat
  | 0, _ => 0
  | n + 1, s => if 0xAA ≤ s.2 then 0 else 1 + flagFrames n (flagStep s)

/-- From `FlagpoleObject`'s `$30`, the flag takes 61 frames if the old byte is at least 61, otherwise 62. -/
theorem flag_frames : ∀ n : Fin 256,
    flagFrames 100 (n.val.toUInt8, 0x30) = if 61 ≤ n.val then 61 else 62 := by
  native_decide

/-! ## 2. A jumping green paratroopa inherits its vertical motion (`InitJumpGPTroopa`, `$C7D1`)

Unlike almost every other init, this one never reaches `InitVStf`, so `Enemy_Y_Speed` and
`Enemy_Y_MoveForce` stay as they were. Together with `erase_keeps` below: an enemy that fell off the
screen is erased at `Y_Speed = 3`, and a paratroopa spawned into its slot starts with that. -/

/-- `$C7D1`–`$C7DD`. -/
def initJumpGPCode : List UInt8 :=
  smbPrg% 0xC7D1 13

/-- An `abs,x` slot array. -/
def absx (base : UInt16) (x : UInt8) : UInt16 := base + x.toUInt16

def JumpGPSummary (x : UInt8) (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xC7DE ∧ t.bad = false ∧
  t.ram (zpx 0x46 x) = 2 ∧ t.ram (zpx 0x58 x) = 0xF8 ∧ t.ram (absx 0x049A x) = 3 ∧
  t.ram (zpx 0xA0 x) = ram (zpx 0xA0 x) ∧ t.ram (absx 0x0434 x) = ram (absx 0x0434 x) ∧
  t.ram (absx 0x0417 x) = ram (absx 0x0417 x) ∧ t.ram (absx 0x0401 x) = ram (absx 0x0401 x) ∧
  t.ram (absx 0x0491 x) = ram (absx 0x0491 x)

set_option maxHeartbeats 40000000 in
theorem jumpGPTroopa_inherits (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xC7D1 ≤ a && a ≤ 0xC7DE) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x47D1 initJumpGPCode)
    (hI : (p &&& 4 == 0) = false) (hx : x < 0x10) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 20)).run ⟨⟨0xC7D1, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ JumpGPSummary x ram t := by
  simp only [CodeAt, initJumpGPCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 20)).run ⟨⟨0xC7D1, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hI] until 51166
  all_goals
    intros
    clear hcode
    subst hrun
    reach_finish [JumpGPSummary, zpx, absx]

/-! ## 3. What `EraseEnemyObject` (`$C998`) clears and keeps

It clears flag, ID, state, floatey control, both timers, shell chain and sprite attributes. It keeps the
motion bytes and the collision bits, which is why a slot freed by it can pass them on. -/

/-- `$C998`–`$C9AE`. -/
def eraseCode : List UInt8 :=
  smbPrg% 0xC998 23

def EraseSummary (x : UInt8) (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xC9AF ∧ t.bad = false ∧
  t.ram (zpx 0x0F x) = 0 ∧ t.ram (zpx 0x16 x) = 0 ∧ t.ram (zpx 0x1E x) = 0 ∧
  t.ram (absx 0x0796 x) = 0 ∧ t.ram (absx 0x078A x) = 0 ∧ t.ram (absx 0x0125 x) = 0 ∧
  t.ram (absx 0x03C5 x) = 0 ∧ t.ram (absx 0x0110 x) = 0 ∧
  t.ram (zpx 0xA0 x) = ram (zpx 0xA0 x) ∧ t.ram (absx 0x0434 x) = ram (absx 0x0434 x) ∧
  t.ram (absx 0x0417 x) = ram (absx 0x0417 x) ∧ t.ram (absx 0x0401 x) = ram (absx 0x0401 x) ∧
  t.ram (absx 0x0491 x) = ram (absx 0x0491 x) ∧ t.ram (zpx 0x3C x) = ram (zpx 0x3C x) ∧
  t.ram (absx 0x03D8 x) = ram (absx 0x03D8 x) ∧ t.ram (absx 0x03A2 x) = ram (absx 0x03A2 x)

set_option maxHeartbeats 40000000 in
theorem erase_keeps (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xC998 ≤ a && a ≤ 0xC9AF) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x4998 eraseCode)
    (hI : (p &&& 4 == 0) = false) (hx : x < 0x06) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 20)).run ⟨⟨0xC998, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ EraseSummary x ram t := by
  simp only [CodeAt, eraseCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 20)).run ⟨⟨0xC998, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hI] until 51631
  all_goals
    intros
    clear hcode
    subst hrun
    reach_finish [EraseSummary, zpx, absx]

/-! ## 4. A leftover contact bit makes the first touch a no-op (`HandlePECollisions`, `$D895`)

With d0 of `Enemy_CollisionBits,x` set, the routine goes straight to its `RTS` without writing
anything: no injury, no stomp, no kick. -/

/-- `$D895`–`$D89E`. -/
def handlePECode : List UInt8 :=
  smbPrg% 0xD895 10

def PESummary (x : UInt8) (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  (ram (absx 0x0491 x) &&& 1 ≠ 0 → t.regs.pc = 0xD8F8) ∧ t.bad = false ∧ t.ram = ram

set_option maxHeartbeats 40000000 in
theorem contact_bit_ignores (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xD895 ≤ a && a ≤ 0xD89F || a == 0xD8F8) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x5895 handlePECode)
    (hI : (p &&& 4 == 0) = false) (hx : x < 0x06) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 8)).run ⟨⟨0xD895, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ PESummary x ram t := by
  simp only [CodeAt, handlePECode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 8)).run ⟨⟨0xD895, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hI] until [55544, 55455]
  all_goals
    intros
    clear hcode
    subst hrun
    reach_finish [PESummary, absx]

/-! ## 5. A power-up inherits its vertical motion (`SetupPowerUp`, `$BC49`)

It writes ID, position, state, flag, bounding box and sprite attributes of slot 5, not `Y_Speed`
(`$A5`), `Y_MoveForce` (`$439`) or `YMF_Dummy` (`$41C`). So a mushroom that walks off a ledge starts falling at
the speed slot 5 held, and a star starts its first bounce with it. -/

/-- `$BC49`–`$BC84`. -/
def setupPowerUpCode : List UInt8 :=
  smbPrg% 0xBC49 60

def PowerUpSummary (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xBC84 ∧ t.bad = false ∧
  t.ram 0x001B = 0x2E ∧ t.ram 0x0014 = 1 ∧ t.ram 0x0023 = 1 ∧
  t.ram 0x00A5 = ram 0x00A5 ∧ t.ram 0x0439 = ram 0x0439 ∧ t.ram 0x041C = ram 0x041C

set_option maxHeartbeats 40000000 in
theorem powerUp_inherits (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xBC49 ≤ a && a ≤ 0xBC84) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x3C49 setupPowerUpCode)
    (hI : (p &&& 4 == 0) = false) (hx : x < 0x10) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xBC49, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ PowerUpSummary ram t := by
  simp only [CodeAt, setupPowerUpCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xBC49, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hI] until 48260
  all_goals
    intros
    clear hcode
    subst hrun
    reach_finish [PowerUpSummary]

end Smb.Routine

#print axioms Smb.Routine.flag_step
#print axioms Smb.Routine.flag_frames
#print axioms Smb.Routine.jumpGPTroopa_inherits
#print axioms Smb.Routine.erase_keeps
#print axioms Smb.Routine.contact_bit_ignores
#print axioms Smb.Routine.powerUp_inherits
