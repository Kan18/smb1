import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# The stomp bounce (`EnemyStompedPts`, `$D996`)

```
EnemyStompedPts:  floatey number for the points (SetupFloateyNumber); SetStun (enemy state, its
                  Y position −2, its Y and X speed, direction); enemy state := $20;
                  InitVStf (enemy Y speed and force := 0); enemy X speed := 0;
                  Player_Y_Speed := $FD
```

Of Mario's vertical state only the speed byte changes: the force (`Y_MoveForce`, the
sub-speed), the sub-pixel and the position are kept. This is the stomp move of the abstract
vertical model (`Smb.Vertical`). Every other write is to the enemy's slot (`base + X`), or
to the floatey-number arrays at `$0110 + X` …, which share the stack page: hence the bounds
on `X` and on the stack pointer.
-/
namespace Smb.Routine

def stompedPtsCode : List UInt8 := smbPrg% 0xD996 29
def floateyCode : List UInt8 := smbPrg% 0xDA11 20
def setStunCode : List UInt8 := smbPrg% 0xE02F 56
def initVStfCode : List UInt8 := smbPrg% 0xC363 8
def playerEnemyDiffCode : List UInt8 := smbPrg% 0xE143 12

def StompSummary (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xD9B2 ∧ t.bad = false ∧ t.ram 0x9F = 0xFD ∧
  t.ram 0x433 = ram 0x433 ∧ t.ram 0x416 = ram 0x416 ∧ t.ram 0xCE = ram 0xCE ∧ t.ram 0xB5 = ram 0xB5

set_option linter.unusedVariables false

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
theorem stomp_reach (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xD996 ≤ a && a ≤ 0xD9B2 || 0xDA11 ≤ a && a ≤ 0xDA24 || 0xE02F ≤ a && a ≤ 0xE066 ||
      0xC363 ≤ a && a ≤ 0xC36A || 0xE143 ≤ a && a ≤ 0xE14E) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x5996 stompedPtsCode) (hfcode : CodeAt prg 0x5A11 floateyCode)
    (hscode : CodeAt prg 0x602F setStunCode) (hicode : CodeAt prg 0x4363 initVStfCode)
    (hpcode : CodeAt prg 0x6143 playerEnemyDiffCode)
    (hI : (p &&& 4 == 0) = false) (hx : x < 0x10) (hsp : 0x40 ≤ sp) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 80)).run ⟨⟨0xD996, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ StompSummary ram t := by
  simp only [CodeAt, stompedPtsCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, floateyCode, UInt16.reduceAdd] at hfcode
  simp only [CodeAt, setStunCode, UInt16.reduceAdd] at hscode
  simp only [CodeAt, initVStfCode, UInt16.reduceAdd] at hicode
  simp only [CodeAt, playerEnemyDiffCode, UInt16.reduceAdd] at hpcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 80)).run ⟨⟨0xD996, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hfcode, hscode, hicode, hpcode, hI] until 55730
  all_goals
    intros
    clear hcode hfcode hscode hicode hpcode
    subst hrun
    reach_finish [StompSummary]


/-! ### Stomping a shell (`HandleStompedShellE` → `SBnce`, `$D9D4`)

```
HandleStompedShellE:  Enemy_State,x := 4; StompChainCounter += 1; floatey number for
                      StompChainCounter + StompTimer; StompTimer += 1;
                      EnemyIntervalTimer,x := RevivalRateData[PrimaryHardMode]
SBnce:                Player_Y_Speed := $FC
```
-/

/-- `$D9D2`–`$D9F5`: `RevivalRateData`, `HandleStompedShellE`, `SBnce`. -/
def stompedShellCode : List UInt8 :=
  smbPrg% 0xD9D2 36

def ShellStompSummary (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xD9F5 ∧ t.bad = false ∧ t.ram 0x9F = 0xFC ∧
  t.ram 0x433 = ram 0x433 ∧ t.ram 0x416 = ram 0x416 ∧ t.ram 0xCE = ram 0xCE ∧ t.ram 0xB5 = ram 0xB5

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
theorem shellStomp_reach (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xD9D4 ≤ a && a ≤ 0xD9F5 || 0xDA11 ≤ a && a ≤ 0xDA24) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x59D2 stompedShellCode) (hfcode : CodeAt prg 0x5A11 floateyCode)
    (hI : (p &&& 4 == 0) = false) (hx : x < 0x10) (hsp : 0x40 ≤ sp) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 60)).run ⟨⟨0xD9D4, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ ShellStompSummary ram t := by
  simp only [CodeAt, stompedShellCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, floateyCode, UInt16.reduceAdd] at hfcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 60)).run ⟨⟨0xD9D4, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hfcode, hI] until 55797
  all_goals
    intros
    clear hcode hfcode
    subst hrun
    reach_finish [ShellStompSummary]

/-! ### Demoting a winged Koopa (`ChkForDemoteKoopa` → `SBnce`, `$D9B3`)

```
ChkForDemoteKoopa:  for an enemy ID ≥ 9: Enemy_ID,x := ID &&& 1; Enemy_State,x := 0; floatey number 3 (400 points);
                    InitVStf; EnemyFacePlayer; Enemy_X_Speed,x := DemotedKoopaXSpdData[direction]
SBnce:              Player_Y_Speed := $FC
```
Mario's vertical state changes as for a shell (`shellStomp_reach`): only the speed byte. 17 of the TAS's 68 stomps take this path.
-/

/-- `$D9B3`–`$D9D1`: `ChkForDemoteKoopa`. -/
def demoteCode : List UInt8 :=
  smbPrg% 0xD9B3 31
/-- `$DA05`–`$DA10`: `EnemyFacePlayer`. -/
def enemyFaceCode : List UInt8 :=
  smbPrg% 0xDA05 12

def DemoteSummary (a x : UInt8) (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xD9F5 ∧ t.bad = false ∧ t.ram 0x9F = 0xFC ∧
  t.ram 0x433 = ram 0x433 ∧ t.ram 0x416 = ram 0x416 ∧ t.ram 0xCE = ram 0xCE ∧ t.ram 0xB5 = ram 0xB5 ∧
  t.ram (0x16 + x).toUInt16 = a &&& 1 ∧ t.ram (0x1E + x).toUInt16 = 0

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
theorem demoteStomp_reach (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xC363 ≤ a && a ≤ 0xC36A || 0xD9B3 ≤ a && a ≤ 0xD9D1 || 0xD9F1 ≤ a && a ≤ 0xD9F5 ||
      0xDA05 ≤ a && a ≤ 0xDA24 || 0xE143 ≤ a && a ≤ 0xE14E) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x59B3 demoteCode) (hscode : CodeAt prg 0x59D2 stompedShellCode)
    (hfacecode : CodeAt prg 0x5A05 enemyFaceCode) (hfcode : CodeAt prg 0x5A11 floateyCode)
    (hicode : CodeAt prg 0x4363 initVStfCode) (hpcode : CodeAt prg 0x6143 playerEnemyDiffCode)
    (hI : (p &&& 4 == 0) = false) (ha : 9 ≤ a) (hx : x < 0x10) (hsp : 0x40 ≤ sp) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 80)).run ⟨⟨0xD9B3, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ DemoteSummary a x ram t := by
  simp only [CodeAt, demoteCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, stompedShellCode, UInt16.reduceAdd] at hscode
  simp only [CodeAt, enemyFaceCode, UInt16.reduceAdd] at hfacecode
  simp only [CodeAt, floateyCode, UInt16.reduceAdd] at hfcode
  simp only [CodeAt, initVStfCode, UInt16.reduceAdd] at hicode
  simp only [CodeAt, playerEnemyDiffCode, UInt16.reduceAdd] at hpcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 80)).run ⟨⟨0xD9B3, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hscode, hfacecode, hfcode, hicode, hpcode, hI] until 55797
  all_goals
    intros
    clear hcode hscode hfacecode hfcode hicode hpcode
    subst hrun
    reach_finish [DemoteSummary]


end Smb.Routine
