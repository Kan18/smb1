import Smb.Data.ProofRom
import Smb.Routine.Climb
import Smb.Routine.Impede
import Smb.Routine.HeadBump

/-!
# Side checks of `PlayerBGCollision` (`DoPlayerSideCheck`, `$DD5E`): walls

The last part of Mario's background collision, which pushes him out of walls. Two passes,
first his left side (`$00 = 2`, probe x+2), then his right side (`$00 = 1`, x+13); each probes an
upper point (y+8 when standing, `BlockBuffer_X/Y_Adder` at `$EB + 3`, `$EB + 5`) and a lower one
(y+24, `$EB + 4`, `$EB + 6`):

```
upper probe, if $20 ≤ Player_Y_Position (≥ $E4: leave at once):
    solid, and not the top of a sideways pipe ($1C, $6B)       → CheckSideMTiles
lower probe, if 8 ≤ Player_Y_Position < $D0 (else leave):
    any nonzero metatile                                        → CheckSideMTiles
CheckSideMTiles: hidden block ($5F, $60)                        → leave
    climbable or not solid (≥ ClimbMTileUpperExt)               → HandleClimbing    (excluded)
    coin ($C2, $C3)                                             → HandleCoinMetatile (excluded)
    jumpspring ($67, $68) while JumpspringAnimCtrl ≠ 0          → leave
    pipe bottom ($6C, $1F), Player_State 0, facing right        → side pipe entry   (excluded)
    otherwise                                                   → ImpedePlayerMove ($00)
```

`sideCheck_call` is a call theorem from `$DD5E` to the RTS that ends `PlayerBGCollision` on these
paths (`ExSCH`, `$DD9B`, if no probe stopped the check; `ExCSM`, `$DE02`, otherwise; the PC is a
`bif` of the inputs). Its RAM is `sideRam`: the scratch bytes (`$00`, `$02`–`$07`, `$EB`, six
stack bytes) are an unspecified witness `w`; everything else is given exactly. `A`, `X`, `Y`,
the flags and the cycle count are left unspecified. The excluded paths are ruled out by
`noSideCoin`, `noSideClimb` and `noSidePipeEntry`, stated on the metatiles at the probes
(`sideTile`) and required only for the probes that run at Mario's height. `sideRam_spec` reads
the result: Mario's vertical state is untouched; at a wall he loses his X speed
(`SideCollisionTimer := 16`) and moves one pixel out, if he was moving into it (`impedeInto`;
speed 0 counts as moving into either wall, speed `$80` into neither).

**Found by the proof attempt.** `jsr BlockBufferColli_Side` is followed directly by `beq`/`bne`:
the caller branches on the Z flag left by `BlockBufferCollision`'s final `lda $03`, which a call
theorem with unknown flags (`blockBufferCollision_call`) does not give. The probe is therefore
executed inline here (`sideProbe0_call`, whose result includes Z).

Proof structure: the probe (`sideProbe_call`) states its results in terms of a *reference* RAM
`R` (the RAM at `$DD5E`; the probes write only scratch bytes), so later probes do not nest the
earlier ones' closed forms; the upper probe with its tests (`upperProbe_call`) and
`CheckSideMTiles` (`csm_call`) are region theorems, so the main run has few paths. The
exclusions reach the symbolic run as proof witnesses of the probe theorems
(`∃ (_ : facts), …`), which `sym_run`'s pruning can use.
-/
namespace Smb.Routine

open Lean Elab Tactic Meta in
/-- On a goal `∃ w, P w` whose body contains a run from a literal state (`Plain.mk …`), supply
that state's RAM as `w`. -/
elab "ram_witness" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOfArity ``Exists 2 do throwError "ram_witness: not ∃"
  let some st := tgt.find? (fun e => e.isAppOfArity ``Plain.mk 5 && !e.hasLooseBVars)
    | throwError "ram_witness: no literal state"
  let ram := st.getArg! 1
  let pred := tgt.appArg!
  let g ← getMainGoal
  let ng ← mkFreshExprSyntheticOpaqueMVar (pred.beta #[ram])
  g.assign (← mkAppOptM ``Exists.intro #[none, some pred, some ram, some ng])
  replaceMainGoal [ng.mvarId!]

/-- The field-by-field part of `call_finish` (after `call_fuel` and any explicit witnesses),
also unfolding `defs` in the final flag conjunct. -/
macro "finish_fields" " [" defs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  repeat apply Exists.intro
  apply And.intro
  · congr 2
    all_goals (try congr 1)
    all_goals (try (is_regs_eq; congr 1))
    all_goals first
      | rfl
      | (funext i; (try sym_exec [bne, $defs,*]); fun_congr; bv_decide (config := { enums := false }))
      | ((try sym_exec [bne, $defs,*]) <;> fun_congr <;> bv_decide (config := { enums := false }))
  · (try sym_exec [bne, $defs,*]) <;> fun_congr <;> bv_decide (config := { enums := false })))

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## The side probe (`BlockBufferColli_Side`, `$E3EC`) -/

/-- RAM after `BlockBufferColli_Side` with `Y = y`, entered with stack pointer `sp`; the values
written are those of the reference RAM `R` (`bbRam` with the side flag 1). -/
def probeRam (R : UInt16 → UInt8) (y sp : UInt8) (prg ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  bif i == 2 then bbRow prg R 0 y
  else bif i == 3 then bbTile prg R 0 y
  else bif i == 4 then bbNybble R 1 0
  else bif i == 5 then bbXSum prg R 0 y
  else bif i == 6 then bbLo prg R 0 y
  else bif i == 7 then 0x05
  else bif i == (0x100 ||| sp.toUInt16) &&& 0x7FF then 1
  else bif i == (0x100 ||| (sp - 1).toUInt16) &&& 0x7FF then 0xE4
  else bif i == (0x100 ||| (sp - 2).toUInt16) &&& 0x7FF then 0x0A
  else bif i == (0x100 ||| (sp - 3).toUInt16) &&& 0x7FF then bbColumn prg R 0 y
  else ram i

section
variable {R ram : UInt16 → UInt8} (h86 : ram 0x86 = R 0x86) (hce : ram 0xCE = R 0xCE)
  (h6d : ram 0x6D = R 0x6D)
include h86 hce h6d

theorem bbXPos_R : bbXPos ram 0 = bbXPos R 0 := by simp only [bbXPos]; exact h86
theorem bbYPos_R : bbYPos ram 0 = bbYPos R 0 := by simp only [bbYPos]; exact hce
theorem bbPage_R : bbPage ram 0 = bbPage R 0 := by simp only [bbPage]; exact h6d

theorem bbTile_R (hbb : ∀ i : UInt16, 0x500 ≤ i → i < 0x800 → ram i = R i) (prg : UInt16 → UInt8)
    (y : UInt8) : bbTile prg ram 0 y = bbTile prg R 0 y := by
  simp only [bbTile, bbAddr, bbRow, bbLo, bbColumn, bbXSum, bbXPos_R h86 hce h6d, bbYPos_R h86 hce h6d,
    bbPage_R h86 hce h6d]
  exact hbb _ (by bv_decide) (by bv_decide)

theorem probeRam_R (hbb : ∀ i : UInt16, 0x500 ≤ i → i < 0x800 → ram i = R i) (prg : UInt16 → UInt8)
    (y sp : UInt8) : probeRam ram y sp prg ram = probeRam R y sp prg ram := by
  funext i
  simp only [probeRam, bbTile_R h86 hce h6d hbb, bbRow, bbLo, bbColumn, bbXSum, bbNybble,
    bbXPos_R h86 hce h6d, bbYPos_R h86 hce h6d, bbPage_R h86 hce h6d]
end

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
/-- `BlockBufferColli_Side` (`lda #1; ldx #0`, then `BlockBufferCollision`), executed inline:
its callers branch on the Z flag of the final `lda $03`, so the flags are part of the result. -/
theorem sideProbe0_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xE3B0 ≤ a && a ≤ 0xE431 || 0x9BDD ≤ a && a ≤ 0x9BF5) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x63B0 blockBufferCode) (hgcode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) (hy : y < 0x1C) :
    ∃ j p' c', ((CPU.runTo (σ := Plain) stop (m + 64)).run ⟨⟨0xE3EC, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xE431, bbTile prg ram 0 y, 0, y, sp, p'⟩,
        probeRam ram y sp prg ram, prg, c', bad⟩).2 ∧
      ((p' &&& 4 == 0) = false ∧ (p' &&& 2 == 0) = (bbTile prg ram 0 y != 0)) := by
  simp only [CodeAt, blockBufferCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, getBlockBufferAddrCode, UInt16.reduceAdd] at hgcode
  -- `BlockBufferAddr`: the address bytes of the two block buffers.
  have hbt : prg 0x1BDD = 0x00 ∧ prg 0x1BDE = 0xD0 ∧ prg 0x1BDF = 0x05 ∧ prg 0x1BE0 = 0x05 := by
    simp [hgcode]
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hbt
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 64)).run ⟨⟨0xE3EC, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hgcode, hI] until 58417
  all_goals
    intros
    clear hcode hgcode
    subst hrun
    (try simp only [bne] at *)
    call_fuel
    finish_fields [probeRam, bbTile, bbAddr, bbRow, bbLo, bbColumn, bbXSum, bbNybble, bbXAdd, bbYAdd,
      bbXPos, bbYPos, bbPage]

/-- The side probe with its values read from the reference RAM `R`, which agrees with the RAM
on Mario's position and the block buffers. The Z flag is a proof witness, so `sym_run` can use
it to prune. -/
theorem sideProbe_call (R : UInt16 → UInt8) (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xE3B0 ≤ a && a ≤ 0xE431 || 0x9BDD ≤ a && a ≤ 0x9BF5) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x63B0 blockBufferCode) (hgcode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) (hy : y < 0x1C)
    (h86 : ram 0x86 = R 0x86) (hce : ram 0xCE = R 0xCE) (h6d : ram 0x6D = R 0x6D)
    (hbb : ∀ i : UInt16, 0x500 ≤ i → i < 0x800 → ram i = R i) :
    ∃ j p' c', ∃ (_ : (p' &&& 2 == 0) = (bbTile prg R 0 y != 0)),
      ((CPU.runTo (σ := Plain) stop (m + 64)).run ⟨⟨0xE3EC, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xE431, bbTile prg R 0 y, 0, y, sp, p'⟩,
        probeRam R y sp prg ram, prg, c', bad⟩).2 ∧ (p' &&& 4 == 0) = false := by
  obtain ⟨j, p', c', h1, h2, hz⟩ := sideProbe0_call stop hstop m a x y sp p ram prg cyc bad hcode hgcode hI hy
  rw [bbTile_R h86 hce h6d hbb] at h1 hz
  rw [probeRam_R h86 hce h6d hbb] at h1
  exact ⟨j, p', c', hz, h1, h2⟩

/-! ## `ImpedePlayerMove` (`$DF4B`) as a call theorem -/

/-- Is Mario moving into the wall on `side` (`$00`: 1 = a wall at the right-side probes,
anything else = the left)? Sign tests of `speed` and `speed − 1`: speed 0 counts as moving into
either wall, speed `$80` into neither. -/
def impedeInto (side : UInt8) (ram : UInt16 → UInt8) : Bool :=
  bif side == 1 then ram 0x57 &&& 0x80 == 0 else (ram 0x57 - 1) &&& 0x80 != 0

/-- `ImpedePlayerMove`'s RAM effect, entered with `$00 = side` (the stack is not touched). -/
def impedeRam (side : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  let pos : UInt16 :=
    ((ram 0x6D).toUInt16 <<< 8 ||| (ram 0x86).toUInt16) + (bif side == 1 then 0xFFFF else 1)
  bif i == 0x490 then ram 0x490 &&& (bif side == 1 then 0xFE else 0xFD)
  else bif impedeInto side ram then
    (bif i == 0x57 then 0 else bif i == 0x785 then 0x10 else bif i == 0x86 then pos.toUInt8
     else bif i == 0x6D then (pos >>> 8).toUInt8 else bif i == 0 then (bif side == 1 then 0xFF else 0)
     else ram i)
  else ram i

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
theorem impede_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xDF4B ≤ a && a ≤ 0xDF8A) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x5F4B impedeCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j p' a' x' y' c', ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xDF4B, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xDF8A, a', x', y', sp, p'⟩, impedeRam (ram 0) ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, impedeCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xDF4B, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI] until 57226
  all_goals
    intros
    clear hcode
    subst hrun
    call_finish [impedeRam, impedeInto]

/-! ## `CheckSideMTiles` (`$DD9C`) as a region theorem -/

/-- `$DD5E`–`$DDCD`: `DoPlayerSideCheck` and `CheckSideMTiles` up to the side pipe entry. -/
def sideCheckCode : List UInt8 :=
  smbPrg% 0xDD5E 112

/-- `$DDFF`–`$DE02`: `StopPlayerMove` and `ExCSM` (RTS). -/
def stopPlayerMoveCode : List UInt8 := smbPrg% 0xDDFF 4

/-- `$DEBD`–`$DEC3`: `ChkInvisibleMTiles`. -/
def chkInvisibleCode : List UInt8 := smbPrg% 0xDEBD 7

/-- `$DEDD`–`$DEE7`: `ChkJumpspringMetatiles`. -/
def chkJumpspringCode : List UInt8 := smbPrg% 0xDEDD 11

/-- Hidden coin / 1-up block (`ChkInvisibleMTiles`): the side check ignores it. -/
def hiddenBlock (t : UInt8) : Bool := t == 0x5F || t == 0x60

/-- A jumpspring metatile while the jumpspring is animating: the side check ignores it. -/
def springBusy (t : UInt8) (ram : UInt16 → UInt8) : Bool := (t == 0x67 || t == 0x68) && ram 0x70E != 0

/-- `CheckSideMTiles` stops Mario (calls `ImpedePlayerMove`) at metatile `t`, given that `t` is
not a coin, not climbable and not a side pipe entry. -/
def blocksSide (t : UInt8) (ram : UInt16 → UInt8) : Bool := !hiddenBlock t && !springBusy t ram

def stackAt (sp k : UInt8) : UInt16 := (0x100 ||| (sp + k).toUInt16) &&& 0x7FF

/-- RAM after `CheckSideMTiles` at metatile `a` (entered by a branch with stack pointer `sp`). -/
def csmRam (a sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  let imp := !hiddenBlock a && !climbable a && !springBusy a ram
  bif i == stackAt sp 0 then (bif imp then 0xDE else 0xDD)
  else bif i == stackAt sp 0xFF then
    (bif hiddenBlock a then 0x9E else bif climbable a then 0xA3 else bif springBusy a ram then 0xB0 else 0x01)
  else bif !hiddenBlock a && i == stackAt sp 0xFE then 0xDF
  else bif !hiddenBlock a && i == stackAt sp 0xFD then 0x9C
  else bif imp then impedeRam (ram 0) ram i else ram i

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 20000 in
/-- `CheckSideMTiles` with a metatile `a` that is neither a coin nor a side pipe entry: to
`ExCSM`'s RTS, or to `HandleClimbing` if `a` is climbable. -/
theorem csm_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xDD9C ≤ a && a ≤ 0xDDCD || 0xDDFF ≤ a && a ≤ 0xDE02 ||
      0xDEBD ≤ a && a ≤ 0xDEC3 || 0xDEDD ≤ a && a ≤ 0xDEE7 || 0xDF4B ≤ a && a ≤ 0xDFB8) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (h1code : CodeAt prg 0x5D5E sideCheckCode) (h2code : CodeAt prg 0x5DFF stopPlayerMoveCode)
    (h3code : CodeAt prg 0x5EBD chkInvisibleCode) (h4code : CodeAt prg 0x5EDD chkJumpspringCode)
    (hcode : CodeAt prg 0x5F4B impedeCode) (htcode : CodeAt prg 0x5F8B tileClassCode)
    (hI : (p &&& 4 == 0) = false) (hcoin : (a == 0xC2 || a == 0xC3) = false)
    (hpipe : (ram 0x1D == 0 && ram 0x33 == 1 && (a == 0x6C || a == 0x1F)) = false) :
    ∃ j p' a' x' y' c', ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0xDD9C, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨bif decide ((bif a < 0x40 then 0x24 else bif a < 0x80 then 0x6D
          else bif a < 0xC0 then 0x8A else 0xC6) ≤ a) then 0xDE2E else 0xDE02, a', x', y', sp, p'⟩,
        csmRam a sp ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  have htab : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6 := by
    have h := htcode; simp only [CodeAt, tileClassCode, UInt16.reduceAdd] at h; simp [h]
  obtain ⟨ht0, ht1, ht2, ht3⟩ := htab
  simp only [CodeAt, sideCheckCode, UInt16.reduceAdd] at h1code
  simp only [CodeAt, stopPlayerMoveCode, UInt16.reduceAdd] at h2code
  simp only [CodeAt, chkInvisibleCode, UInt16.reduceAdd] at h3code
  simp only [CodeAt, chkJumpspringCode, UInt16.reduceAdd] at h4code
  simp only [CodeAt, tileClassCode, UInt16.reduceAdd] at htcode
  have hirts : prg 0x5F8A = 0x60 := by
    have h := hcode; simp only [CodeAt, impedeCode, UInt16.reduceAdd] at h; simp [h]
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0xDD9C, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [h1code, h2code, h3code, h4code, htcode, hirts, hI, impedeRam, impedeInto]
    until [56834, 56878] calls [impede_call]
  all_goals
    intros
    clear h1code h2code h3code h4code htcode hirts hcode
    subst hrun
    call_finish [csmRam, stackAt, hiddenBlock, climbable, climbExt, springBusy, impedeRam, impedeInto]

/-! ## The side check -/

/-- Mario's metatile at side probe `k` of `DoPlayerSideCheck` (adder offset `$EB + k`): 3 and 4
are his left side (upper, lower), 5 and 6 his right side. -/
def sideTile (prg ram : UInt16 → UInt8) (k : UInt8) : UInt8 := bbTile prg ram 0 (ram 0xEB + k)

def isCoin (t : UInt8) : Bool := t == 0xC2 || t == 0xC3

/-- The bottom of a sideways pipe (`$6C`, `$1F`) while Mario is in the normal state and facing
right: `CheckSideMTiles` starts the side pipe entry. -/
def pipeEntry (ram : UInt16 → UInt8) (t : UInt8) : Bool :=
  ram 0x1D == 0 && ram 0x33 == 1 && (t == 0x6C || t == 0x1F)

/-- Heights at which the upper probes (3, 5) and the lower probes (4, 6) run. -/
def upperProbes (ram : UInt16 → UInt8) : Bool := decide (0x20 ≤ ram 0xCE) && decide (ram 0xCE < 0xE4)
def lowerProbes (ram : UInt16 → UInt8) : Bool := decide (8 ≤ ram 0xCE) && decide (ram 0xCE < 0xD0)

/-- Excludes `HandleCoinMetatile`: a coin at a probe that runs (collected, `GiveOneCoin`). -/
def noSideCoin (prg ram : UInt16 → UInt8) : Bool :=
  (!upperProbes ram || !isCoin (sideTile prg ram 3) && !isCoin (sideTile prg ram 5)) &&
  (!lowerProbes ram || !isCoin (sideTile prg ram 4) && !isCoin (sideTile prg ram 6))

/-- Excludes `HandleClimbing`: a climbable or other non-solid metatile (`climbable`: vine,
flagpole, …) at a lower probe that runs. At an upper probe the code itself skips them. -/
def noSideClimb (prg ram : UInt16 → UInt8) : Bool :=
  !lowerProbes ram || !climbable (sideTile prg ram 4) && !climbable (sideTile prg ram 6)

/-- Excludes the side pipe entry (`PipeDwnS`, see `pipeEntry`) at a probe that runs. -/
def noSidePipeEntry (prg ram : UInt16 → UInt8) : Bool :=
  (!upperProbes ram || !pipeEntry ram (sideTile prg ram 3) && !pipeEntry ram (sideTile prg ram 5)) &&
  (!lowerProbes ram || !pipeEntry ram (sideTile prg ram 4) && !pipeEntry ram (sideTile prg ram 6))

/-- An upper probe finds a wall: a solid metatile other than the top of a sideways pipe. -/
def upperHit (t : UInt8) : Bool := t != 0 && t != 0x1C && t != 0x6B && !climbable t

/-- The probe that ends the side check (0: none). Pass 1 probes the left side, pass 2 the right;
a lower probe stops at any nonzero metatile. -/
def sideHitProbe (prg ram : UInt16 → UInt8) : UInt8 :=
  let h := ram 0xCE
  bif decide (0xE4 ≤ h) then 0
  else bif decide (0x20 ≤ h) && upperHit (sideTile prg ram 3) then 3
  else bif decide (h < 8) || decide (0xD0 ≤ h) then 0
  else bif sideTile prg ram 4 != 0 then 4
  else bif decide (0x20 ≤ h) && upperHit (sideTile prg ram 5) then 5
  else bif sideTile prg ram 6 != 0 then 6
  else 0

/-- `$00` for `ImpedePlayerMove`: 2 for a wall on the left, 1 on the right. -/
def sideOf (prg ram : UInt16 → UInt8) : UInt8 := bif sideHitProbe prg ram < 5 then 2 else 1

/-- The side check calls `ImpedePlayerMove`. -/
def sideBlocks (prg ram : UInt16 → UInt8) : Bool :=
  sideHitProbe prg ram != 0 && blocksSide (sideTile prg ram (sideHitProbe prg ram)) ram

/-- Scratch bytes: `$00`, `$02`–`$07`, `$EB` and the six stack bytes from `sp` down. -/
def sideScratch (sp : UInt8) (i : UInt16) : Bool :=
  i == 0 || i == 2 || i == 3 || i == 4 || i == 5 || i == 6 || i == 7 || i == 0xEB || i == stackAt sp 0 || i == stackAt sp 0xFF ||
  i == stackAt sp 0xFE || i == stackAt sp 0xFD || i == stackAt sp 0xFC || i == stackAt sp 0xFB

/-- RAM after the side check; the scratch bytes are left to `w`. -/
def sideRam (w : UInt16 → UInt8) (sp : UInt8) (prg ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  bif sideScratch sp i then w i
  else bif sideBlocks prg ram then impedeRam (sideOf prg ram) ram i else ram i

/-- Probe `y` (adder offset) runs, by height. -/
def probeRuns (ram : UInt16 → UInt8) (y : UInt8) : Bool :=
  (y - ram 0xEB == 3 || y - ram 0xEB == 5) && upperProbes ram ||
  (y - ram 0xEB == 4 || y - ram 0xEB == 6) && lowerProbes ram

/-- The exclusions at probe `y`. -/
def probeOk (prg ram : UInt16 → UInt8) (y : UInt8) : Bool :=
  !isCoin (bbTile prg ram 0 y) && !pipeEntry ram (bbTile prg ram 0 y) &&
  (y - ram 0xEB == 3 || y - ram 0xEB == 5 || !climbable (bbTile prg ram 0 y))

theorem probeOk_of {prg ram : UInt16 → UInt8} (hcoin : noSideCoin prg ram = true)
    (hclimb : noSideClimb prg ram = true) (hpipe : noSidePipeEntry prg ram = true) :
    ∀ y, probeRuns ram y = true → probeOk prg ram y = true := by
  intro y hr
  simp only [probeRuns, probeOk] at hr ⊢
  generalize hk : y - ram 0xEB = k at hr ⊢
  have hy : y = ram 0xEB + k := by bv_decide
  subst hy
  simp only [noSideCoin, noSideClimb, noSidePipeEntry, sideTile] at hcoin hclimb hpipe
  have : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by
    revert hr; cases upperProbes ram <;> cases lowerProbes ram <;> simp <;> bv_decide
  rcases this with rfl | rfl | rfl | rfl <;>
    revert hr hcoin hclimb hpipe <;>
    generalize upperProbes ram = u <;> generalize lowerProbes ram = l <;>
    generalize bbTile prg ram 0 (ram 0xEB + 3) = t3 <;> generalize bbTile prg ram 0 (ram 0xEB + 4) = t4 <;>
    generalize bbTile prg ram 0 (ram 0xEB + 5) = t5 <;> generalize bbTile prg ram 0 (ram 0xEB + 6) = t6 <;>
    simp only [isCoin, pipeEntry, climbable, climbExt] <;> bv_decide

/-- A probe that runs, with its exclusions (and the Z flag) as a proof witness. -/
theorem sideProbeOk_call (R : UInt16 → UInt8) (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xE3B0 ≤ a && a ≤ 0xE431 || 0x9BDD ≤ a && a ≤ 0x9BF5) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x63B0 blockBufferCode) (hgcode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) (hy : y < 0x1C)
    (h86 : ram 0x86 = R 0x86) (hce : ram 0xCE = R 0xCE) (h6d : ram 0x6D = R 0x6D)
    (hbb : ∀ i : UInt16, 0x500 ≤ i → i < 0x800 → ram i = R i)
    (hok : ∀ y, probeRuns R y = true → probeOk prg R y = true) (hruns : probeRuns R y = true) :
    ∃ j p' c', ∃ (_ : (p' &&& 2 == 0) = (bbTile prg R 0 y != 0) ∧
        (bbTile prg R 0 y == 0xC2 || bbTile prg R 0 y == 0xC3) = false ∧
        (R 0x1D == 0 && R 0x33 == 1 && (bbTile prg R 0 y == 0x6C || bbTile prg R 0 y == 0x1F)) = false ∧
        (y - R 0xEB == 3 || y - R 0xEB == 5 || !decide ((bif bbTile prg R 0 y < 0x40 then 0x24
          else bif bbTile prg R 0 y < 0x80 then 0x6D else bif bbTile prg R 0 y < 0xC0 then 0x8A else 0xC6) ≤
          bbTile prg R 0 y)) = true),
      ((CPU.runTo (σ := Plain) stop (m + 64)).run ⟨⟨0xE3EC, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xE431, bbTile prg R 0 y, 0, y, sp, p'⟩,
        probeRam R y sp prg ram, prg, c', bad⟩).2 ∧ (p' &&& 4 == 0) = false := by
  have hq := hok y hruns
  simp only [probeOk, isCoin, pipeEntry, climbable, climbExt, Bool.and_eq_true, Bool.not_eq_true'] at hq
  obtain ⟨j, p', c', hz, h1, h2⟩ :=
    sideProbe_call R stop hstop m a x y sp p ram prg cyc bad hcode hgcode hI hy h86 hce h6d hbb
  exact ⟨j, p', c', ⟨hz, hq.1.1, hq.1.2, hq.2⟩, h1, h2⟩

/-- RAM after an upper probe and its tests (`$DD73`–`$DD84`), with stack pointer `sp` at the
JSR: the probe's writes, its return address, and those of `CheckForClimbMTiles` /
`GetMTileAttrib` unless the metatile is 0, `$1C` or `$6B`. -/
def upperRam (R : UInt16 → UInt8) (y sp : UInt8) (prg ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  let t := bbTile prg R 0 y
  let chk := !(t == 0 || t == 0x1C || t == 0x6B)
  bif i == stackAt sp 0 then 0xDD
  else bif i == stackAt sp 0xFF then (bif chk then 0x82 else 0x75)
  else bif chk && i == stackAt sp 0xFE then 0xDF
  else bif chk && i == stackAt sp 0xFD then 0x9C
  else probeRam R y (sp + 0xFE) prg ram i

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 20000 in
/-- An upper probe and its tests, from the JSR at `$DD73` to `CheckSideMTiles` (a wall,
`upperHit`) or `BHalf` (`$DD85`). -/
theorem upperProbe_call (R : UInt16 → UInt8) (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xDD73 ≤ a && a ≤ 0xDD84 || 0xDF9A ≤ a && a ≤ 0xDFB8 || 0xE3B0 ≤ a && a ≤ 0xE431 ||
      0x9BDD ≤ a && a ≤ 0x9BF5) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (h1code : CodeAt prg 0x5D5E sideCheckCode) (htcode : CodeAt prg 0x5F8B tileClassCode)
    (hcode : CodeAt prg 0x63B0 blockBufferCode) (hgcode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) (hy : y < 0x1C)
    (h86 : ram 0x86 = R 0x86) (hce : ram 0xCE = R 0xCE) (h6d : ram 0x6D = R 0x6D)
    (hbb : ∀ i : UInt16, 0x500 ≤ i → i < 0x800 → ram i = R i)
    (hok : ∀ y, probeRuns R y = true → probeOk prg R y = true) (hruns : probeRuns R y = true) :
    ∃ j, ∃ (_ : (bbTile prg R 0 y == 0xC2 || bbTile prg R 0 y == 0xC3) = false ∧
        (R 0x1D == 0 && R 0x33 == 1 && (bbTile prg R 0 y == 0x6C || bbTile prg R 0 y == 0x1F)) = false),
      ∃ p' x' y' c',
      ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0xDD73, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨bif (bbTile prg R 0 y != 0 && bbTile prg R 0 y != 0x1C &&
          bbTile prg R 0 y != 0x6B && !decide ((bif bbTile prg R 0 y < 0x40 then 0x24
          else bif bbTile prg R 0 y < 0x80 then 0x6D else bif bbTile prg R 0 y < 0xC0 then 0x8A else 0xC6) ≤
          bbTile prg R 0 y)) then 0xDD9C else 0xDD85, bbTile prg R 0 y, x', y', sp, p'⟩,
        upperRam R y sp prg ram, prg, c', bad⟩).2 ∧ (p' &&& 4 == 0) = false := by
  have hQ : (bbTile prg R 0 y == 0xC2 || bbTile prg R 0 y == 0xC3) = false ∧
      (R 0x1D == 0 && R 0x33 == 1 && (bbTile prg R 0 y == 0x6C || bbTile prg R 0 y == 0x1F)) = false := by
    have hq := hok y hruns
    simp only [probeOk, isCoin, pipeEntry, Bool.and_eq_true, Bool.not_eq_true'] at hq
    exact hq.1
  -- The block buffers as the probe sees them, behind this region's JSR (stated in the form the
  -- probe's hypothesis takes at the call, so that `assumption` discharges it).
  have hbb' : ∀ i : UInt16, 1280 ≤ i → i < 2048 →
      (bif i == (256 ||| (sp + 255).toUInt16) &&& 2047 then 117
        else bif i == (256 ||| sp.toUInt16) &&& 2047 then 221 else ram i) = R i := by
    intro i h1 h2
    have e1 : (i == (256 ||| (sp + 255).toUInt16) &&& 2047) = false := by bv_decide
    have e2 : (i == (256 ||| sp.toUInt16) &&& 2047) = false := by bv_decide
    rw [e1, e2]; exact hbb i h1 h2
  have hprobe := sideProbe_call R
  revert hprobe; intro hprobe
  have htab : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6 := by
    have h := htcode; simp only [CodeAt, tileClassCode, UInt16.reduceAdd] at h; simp [h]
  obtain ⟨ht0, ht1, ht2, ht3⟩ := htab
  have hrts : prg 0x6431 = 0x60 := by
    have h := hcode; simp only [CodeAt, blockBufferCode, UInt16.reduceAdd] at h; simp [h]
  have h1 := h1code; simp only [CodeAt, sideCheckCode, UInt16.reduceAdd] at h1
  have ht := htcode; simp only [CodeAt, tileClassCode, UInt16.reduceAdd] at ht
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0xDD73, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [h1, ht, hrts, hI, probeRam, stackAt] until [56732, 56709] calls [hprobe]
  all_goals
    intros
    clear h1 ht hrts h1code htcode hcode hgcode hok hprobe hbb'
    subst hrun
    (try simp only [bne] at *)
    call_fuel
    refine ⟨by bv_decide (config := { enums := false }), ?_⟩
    finish_fields [upperRam, probeRam, stackAt]

/-- Finish a path of `sideCheck_call`: the scratch witness is the path's own RAM. -/
macro "side_finish" " [" defs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  (try simp only [bne] at *)
  call_fuel
  ram_witness
  finish_fields [$defs,*]))

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 40000 in
/-- `DoPlayerSideCheck` to the RTS of `PlayerBGCollision` (`$DD9B` if no probe stopped the
check, else `$DE02`), with the coin, climbing and side pipe paths excluded. -/
theorem sideCheck_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xDD5E ≤ a && a ≤ 0xDDCD || 0xDDFF ≤ a && a ≤ 0xDE02 || 0xDEBD ≤ a && a ≤ 0xDEC3 ||
      0xDEDD ≤ a && a ≤ 0xDEE7 || 0xDF4B ≤ a && a ≤ 0xDFB8 || 0xE3B0 ≤ a && a ≤ 0xE431 ||
      0x9BDD ≤ a && a ≤ 0x9BF5) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (h1code : CodeAt prg 0x5D5E sideCheckCode) (h2code : CodeAt prg 0x5DFF stopPlayerMoveCode)
    (h3code : CodeAt prg 0x5EBD chkInvisibleCode) (h4code : CodeAt prg 0x5EDD chkJumpspringCode)
    (hcode : CodeAt prg 0x5F4B impedeCode) (htcode : CodeAt prg 0x5F8B tileClassCode)
    (hbcode : CodeAt prg 0x63B0 blockBufferCode) (hgcode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) (heb : ram 0xEB < 0x16)
    (hcoin : noSideCoin prg ram = true) (hclimb : noSideClimb prg ram = true)
    (hpipe : noSidePipeEntry prg ram = true) :
    ∃ j w p' a' x' y' c', ((CPU.runTo (σ := Plain) stop (m + 600)).run ⟨⟨0xDD5E, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨bif sideHitProbe prg ram == 0 then 0xDD9B else 0xDE02, a', x', y', sp, p'⟩,
        sideRam w sp prg ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  have hok := probeOk_of hcoin hclimb hpipe
  have hprobe := sideProbeOk_call ram
  have hupper := upperProbe_call ram
  revert hprobe hupper; intro hprobe hupper
  have htab : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6 := by
    have h := htcode; simp only [CodeAt, tileClassCode, UInt16.reduceAdd] at h; simp [h]
  obtain ⟨ht0, ht1, ht2, ht3⟩ := htab
  have hrts : prg 0x6431 = 0x60 := by
    have h := hbcode; simp only [CodeAt, blockBufferCode, UInt16.reduceAdd] at h; simp [h]
  have h1 := h1code; simp only [CodeAt, sideCheckCode, UInt16.reduceAdd] at h1
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 600)).run ⟨⟨0xDD5E, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [h1, hrts, hI, probeRam, upperRam, stackAt, probeRuns, upperProbes, lowerProbes]
    until [56731, 56834, 56878] calls [hupper, hprobe, csm_call]
  all_goals
    intros
    clear h1 hrts h1code h2code h3code h4code hcode htcode hbcode hgcode hok hprobe hupper
    subst hrun
    simp only [noSideCoin, noSideClimb, noSidePipeEntry, sideTile, upperProbes, lowerProbes, isCoin,
      pipeEntry, climbable, climbExt] at hcoin hclimb hpipe
    simp only [bbTile, bbAddr, bbRow, bbLo, bbColumn, bbXSum, bbNybble, bbXAdd, bbYAdd, bbXPos, bbYPos,
      bbPage] at *
    side_finish [sideRam, sideScratch, stackAt, sideBlocks, sideOf, sideHitProbe, sideTile, upperHit,
      blocksSide, hiddenBlock, springBusy, climbable, climbExt, impedeRam, impedeInto, csmRam, upperRam,
      probeRam, bbTile, bbAddr, bbRow, bbLo, bbColumn, bbXSum, bbNybble, bbXAdd, bbYAdd, bbXPos, bbYPos,
      bbPage]

/-- How the side check moves Mario, read off the closed form. His vertical state (speed, force,
sub-pixel, position, height) is untouched. Without a wall (`sideBlocks` false: no probe hit, a
hidden block, or a jumpspring that is animating) only scratch bytes change. At a wall on side
`s = sideOf` (2: left probes, 1: right probes) its bit of `Player_CollisionBits` is cleared; if
he is moving into the wall (`impedeInto`), his X speed becomes 0, `SideCollisionTimer` 16, and
he moves one pixel away from it (16-bit `PageLoc:X_Position`), else speed and position stay.
Nothing else changes. -/
theorem sideRam_spec (w : UInt16 → UInt8) (sp : UInt8) (prg ram : UInt16 → UInt8) :
    let r := sideRam w sp prg ram
    let s := sideOf prg ram
    let pos : UInt16 := (ram 0x6D).toUInt16 <<< 8 ||| (ram 0x86).toUInt16
    let pos' : UInt16 := (r 0x6D).toUInt16 <<< 8 ||| (r 0x86).toUInt16
    (r 0x9F = ram 0x9F ∧ r 0x433 = ram 0x433 ∧ r 0x416 = ram 0x416 ∧ r 0xCE = ram 0xCE ∧
      r 0xB5 = ram 0xB5) ∧
    (sideBlocks prg ram = false → ∀ i, sideScratch sp i = false → r i = ram i) ∧
    (sideBlocks prg ram = true →
      r 0x490 = ram 0x490 &&& (bif s == 1 then 0xFE else 0xFD) ∧
      (impedeInto s ram = true →
        r 0x57 = 0 ∧ r 0x785 = 0x10 ∧ pos' = (bif s == 1 then pos - 1 else pos + 1)) ∧
      (impedeInto s ram = false → r 0x57 = ram 0x57 ∧ r 0x785 = ram 0x785 ∧ pos' = pos) ∧
      ∀ i, sideScratch sp i = false → i ≠ 0x490 → i ≠ 0x57 → i ≠ 0x785 → i ≠ 0x86 → i ≠ 0x6D →
        r i = ram i) := by
  simp only [sideRam, impedeRam, sideScratch, stackAt]
  generalize sideBlocks prg ram = b
  generalize sideOf prg ram = s
  generalize impedeInto s ram = d
  refine ⟨?_, fun hb i hi => ?_, fun hb => ⟨?_, fun hd => ?_, fun hd => ?_, fun i hi h1 h2 h3 h4 h5 => ?_⟩⟩ <;>
    (try subst hb) <;> (try subst hd) <;> (try revert hi) <;> bv_decide (config := { enums := false })

end Smb.Routine
