import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# `BlockBufferCollision` (`$E3F0`): which metatile is at a point of an object

Every background collision test goes through this routine. With `X` = object offset,
`Y` = index into the adder tables (which point of the object), and `A` = 0 (return the
vertical sub-tile offset) or 1 (horizontal):

```
$05  := X_Adder[Y] + X_Position,x;  column := ((PageLoc,x + carry) & 1) << 4 | $05 >> 4
$06/$07 := Block_Buffer_1 ($0500) or _2 ($05D0) + column & 15      (GetBlockBufferAddr)
$02  := ((Y_Position,x + Y_Adder[Y]) & $F0) − $20                  (row; status bar is 32 px)
$03  := metatile at ($06),$02;  $04 := (Y_Position,x or X_Position,x) & 15;  A := $03
```
-/
namespace Smb.Routine

/-- `$E3B0`–`$E431`: `BlockBuffer_X_Adder`, `BlockBuffer_Y_Adder`, the entry points, and
`BlockBufferCollision` with its RTS. -/
def blockBufferCode : List UInt8 :=
  smbPrg% 0xE3B0 130

/-- `$9BDD`–`$9BF5`: `BlockBufferAddr` and `GetBlockBufferAddr` with its RTS. -/
def getBlockBufferAddrCode : List UInt8 :=
  smbPrg% 0x9BDD 25

def bbXAdd (prg : UInt16 → UInt8) (y : UInt8) : UInt8 := prg ((0xE3B0 + y.toUInt16) &&& 0x7FFF)
def bbYAdd (prg : UInt16 → UInt8) (y : UInt8) : UInt8 := prg ((0xE3CC + y.toUInt16) &&& 0x7FFF)

def bbXPos (ram : UInt16 → UInt8) (x : UInt8) : UInt8 := ram ((0x86 + x).toUInt16 &&& 0x7FF)
def bbYPos (ram : UInt16 → UInt8) (x : UInt8) : UInt8 := ram ((0xCE + x).toUInt16 &&& 0x7FF)
def bbPage (ram : UInt16 → UInt8) (x : UInt8) : UInt8 := ram ((0x6D + x).toUInt16 &&& 0x7FF)

/-- `$05`: the probe's horizontal pixel within the page. -/
def bbXSum (prg ram : UInt16 → UInt8) (x y : UInt8) : UInt8 := bbXAdd prg y + bbXPos ram x

/-- Block-buffer column, 0–31. -/
def bbColumn (prg ram : UInt16 → UInt8) (x y : UInt8) : UInt8 :=
  let c : UInt8 := bif (bbXAdd prg y).toUInt16 + (bbXPos ram x).toUInt16 > 0xFF then 1 else 0
  (((bbPage ram x + c) &&& 1) <<< 4) ||| (bbXSum prg ram x y >>> 4)

/-- `$06`: low byte of the column's address. -/
def bbLo (prg ram : UInt16 → UInt8) (x y : UInt8) : UInt8 :=
  let col := bbColumn prg ram x y
  (col &&& 0x0F) + (bif col >>> 4 == 0 then 0x00 else 0xD0)

/-- `$02`: the row's offset in the block buffer. -/
def bbRow (prg ram : UInt16 → UInt8) (x y : UInt8) : UInt8 :=
  ((bbYPos ram x + bbYAdd prg y) &&& 0xF0) - 0x20

def bbAddr (prg ram : UInt16 → UInt8) (x y : UInt8) : UInt16 :=
  ((0x05 : UInt16) <<< 8 ||| (bbLo prg ram x y).toUInt16) + (bbRow prg ram x y).toUInt16

/-- The metatile found (`$03` and `A`). -/
def bbTile (prg ram : UInt16 → UInt8) (x y : UInt8) : UInt8 := ram (bbAddr prg ram x y &&& 0x7FF)

/-- `$04`: the sub-tile offset, vertical (`A = 0`) or horizontal. -/
def bbNybble (ram : UInt16 → UInt8) (flag x : UInt8) : UInt8 :=
  (bif flag == 0 then bbYPos ram x else bbXPos ram x) &&& 0x0F

def bbRam (flag x y sp : UInt8) (prg ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  bif i == 2 then bbRow prg ram x y
  else bif i == 3 then bbTile prg ram x y
  else bif i == 4 then bbNybble ram flag x
  else bif i == 5 then bbXSum prg ram x y
  else bif i == 6 then bbLo prg ram x y
  else bif i == 7 then 0x05
  else bif i == (0x100 ||| sp.toUInt16) &&& 0x7FF then flag
  else bif i == (0x100 ||| (sp - 1).toUInt16) &&& 0x7FF then 0xE4
  else bif i == (0x100 ||| (sp - 2).toUInt16) &&& 0x7FF then 0x0A
  else bif i == (0x100 ||| (sp - 3).toUInt16) &&& 0x7FF then bbColumn prg ram x y
  else ram i

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
theorem blockBufferCollision_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xE3B0 ≤ a && a ≤ 0xE431 || 0x9BDD ≤ a && a ≤ 0x9BF5) = true → a ≠ stop)
    (m : Nat) (flag x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x63B0 blockBufferCode) (hgcode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) (hx : x < 0x32) (hy : y < 0x1C) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 60)).run ⟨⟨0xE3F0, flag, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xE431, bbTile prg ram x y, x, y, sp, p'⟩,
        bbRam flag x y sp prg ram, prg,
        cyc + (bif flag != 0 then 141 else 143) +
          (bif (bbLo prg ram x y).toUInt16 + (bbRow prg ram x y).toUInt16 > 0xFF then 1 else 0),
        bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, blockBufferCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, getBlockBufferAddrCode, UInt16.reduceAdd] at hgcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 60)).run ⟨⟨0xE3F0, flag, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hgcode, hI] until 58417
  all_goals
    intros
    subst hrun
    call_finish [bbRam, bbTile, bbAddr, bbRow, bbLo, bbColumn, bbXSum, bbNybble, bbXAdd, bbYAdd, bbXPos,
      bbYPos, bbPage]

end Smb.Routine
