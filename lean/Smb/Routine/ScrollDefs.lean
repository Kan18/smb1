import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# `ScrollHandler` (`$AF93`): screen scrolling and Mario's clamp at the screen edges

`PlayerCtrlRoutine` calls it every frame (`$B14C`) after Mario has moved, with
`Player_X_Scroll` (`$06FF`) holding the pixels he moved (stored by the caller from
`MovePlayerHorizontally`'s `A`) and `Player_Pos_ForScroll` (`$0755`) his on-screen X.

```
ScrollHandler:  Player_X_Scroll += Platform_X_Scroll
                if ScrollLock ($0723) = 0 ∧ Player_Pos_ForScroll ≥ $50 ∧ SideCollisionTimer ($0785) = 0
                   ∧ Player_X_Scroll ∈ [1, $80]:
                  amt := Player_X_Scroll, minus 1 if ≥ 2, unless Player_Pos_ForScroll ≥ $70
                  ScrollAmount := amt; ScrollThirtyTwo += amt
                  ScreenLeft (page:x) += amt; HorizontalScroll := its x; PPU_CTRL mirror bit 0 := page & 1
                  ScreenRight := ScreenLeft + 255 (GetScreenPosition); ScrollIntervalTimer := 8
                else ScrollAmount := 0
ChkPOffscr:     bits := GetXOffscreenBits (X = 0, Mario);  $00 := bits
                bit 7 of bits → KeepOnscr with y = 0 (left edge)
                else bit 5    → KeepOnscr with y = 1 (right edge)
KeepOnscr:      Mario (page:x) := ScreenEdge[y] − (0, $10)[y]
                if Left_Right_Buttons ($0C) ≠ (1, 2)[y]: Player_X_Speed := 0
InitPlatScrl:   Platform_X_Scroll := 0; rts
```

`GetXOffscreenBits` (`$F1F6`, here with its own call theorem) compares the object's 16-bit
position `P` with the right edge `R`, then (if that gives 0) the left edge `L`, and returns a
byte from `XOffscreenBitsData`. In terms of the 16-bit differences (`offBits_right`,
`offBits_left`): right side `$FF` if `R − P ≥ $8000` (bit 7), a byte with bit 5 if
`R − P < $10`, 0 if `$38 ≤ R − P < $8000`; left side 0 if `L − P ≥ $8000`, else bit 7 set.

Proved here:
- `getXOffscreenBits_call`, `scrollHandler_call`: call theorems (closed form at the RTS,
  `$F22A` / `$B033`, exact cycles), for `sym_run … calls […]`. Pass `scrollRam`, `gxoRam`
  and `scrMid` to the caller's `sym_run` simp facts, so its RTS reads the return address
  through the closed-form RAM. No precondition on RAM is needed (`getXOffscreenBits_call` needs the
  object offset `X < $7A`; `ScrollHandler` uses `X = 0`).
- `scrollRam_spec`: the effect on Mario. With `L`, `R` the screen edges after the scroll and
  `P` Mario's position (`Player_PageLoc : Player_X_Position`), all mod 2^16:
  * `R − P ≥ $8000`, or `$38 ≤ R − P` and `L − P < $8000`: `P := L` (left clamp);
  * `R − P < $10`: `P := R − $10` (right clamp);
  * otherwise `P` unchanged.
  `Player_X_Speed` is zeroed on a left clamp unless `Left_Right_Buttons = 1` (right only), on
  a right clamp unless it is 2 (left only). The sub-pixel `$0400` and the vertical state
  (`$9F`, `$0433`, `$0416`, `$CE`, `$B5`) are unchanged, as is every byte outside a short list.
- `scrollRam_clamp`: the same when `R = L + 255` (`screenEdgesConsistent`, automatic when the
  screen scrolls), in terms of Mario's offset `D = P − L` from the left edge: `D = 0` or
  `D ≥ $100` → `P := L`; `$F0 ≤ D < $100` → `P := L + $EF`; else unchanged.

**Found:** the first case includes Mario being *right* of the right edge (`R − P ≥ $8000`,
i.e. `$100 ≤ D ≤ $80FF`): `GetXOffscreenBits` returns `$FF` for the right side, whose bit 7
`ScrollHandler` reads as "beyond the left edge", so Mario is moved to the left edge, not the
right one. Whether any input sequence puts him there (he would have to pass `R − $10` by more
than 16 pixels in one frame, or the edge bytes must be inconsistent) is open. Also: standing
exactly on the left edge (`D = 0`) zeroes the speed unless only Right is held.
-/
namespace Smb.Routine

/-! ## `GetXOffscreenBits` -/

/-- `$F1E3`–`$F1F2` (`XOffscreenBitsData`), read at a computed index. -/
def xOffscreenBitsData : List UInt8 :=
  smbPrg% 0xF1E3 16

/-- `$F1F3`–`$F22A`: `DefaultXOnscreenOfs` and `GetXOffscreenBits` with its RTS. -/
def getXOffscreenBitsCode : List UInt8 :=
  smbPrg% 0xF1F3 56

/-- `$F26D`–`$F281` (`DividePDiff`, with its RTS). -/
def dividePDiffCode : List UInt8 :=
  smbPrg% 0xF26D 21

/-- The high byte of `edge − object` (page difference minus the borrow from the pixels). -/
def edgePageDiff (ex ep ox op : UInt8) : UInt8 := ep - op - (bif ex < ox then 1 else 0)

/-- The offscreen bits for one edge (`right`: `y = 1`, the right edge; else the left one).
Page difference negative: table index `DefaultXOnscreenOfs[y]`; zero and pixel difference
`d < $38`: `DividePDiff` gives index `d >> 3` (right) or `8 + d >> 3` (left); otherwise
`DefaultXOnscreenOfs[y + 1]`. -/
def offBits (right : Bool) (ex ep ox op : UInt8) : UInt8 :=
  let d := ex - ox
  let pd := edgePageDiff ex ep ox op
  bif pd &&& 0x80 != 0 then (bif right then 0xFF else 0x00)
  else bif pd == 0 && d < 0x38 then
    (bif right then (0x7F : UInt8) >>> (d >>> 3) else ~~~((0x7F : UInt8) >>> (d >>> 3)))
  else (bif right then 0x00 else 0xFF)

/-- Does this edge's test call `DividePDiff` (page difference 0)? -/
def offDiv (ex ep ox op : UInt8) : Bool := edgePageDiff ex ep ox op == 0

/-- Cycles of one loop iteration, from `XOfsLoop` to the `cmp #0` after `XLdBData`. -/
def offCyc (right : Bool) (ex ep ox op : UInt8) : UInt64 :=
  let pd := edgePageDiff ex ep ox op
  bif pd &&& 0x80 != 0 then 39 else bif pd != 0 then 47 else bif ex - ox ≥ 0x38 then 77
  else bif right then 91 else 93

def objX (ram : UInt16 → UInt8) (x : UInt8) : UInt8 := ram ((0x86 + x).toUInt16 &&& 0x7FF)
def objPage (ram : UInt16 → UInt8) (x : UInt8) : UInt8 := ram ((0x6D + x).toUInt16 &&& 0x7FF)

/-- Right-edge bits (`ScreenRight_X_Pos` `$071D`, `ScreenRight_PageLoc` `$071B`). -/
def gxoR (ram : UInt16 → UInt8) (x : UInt8) : UInt8 :=
  offBits true (ram 0x71D) (ram 0x71B) (objX ram x) (objPage ram x)
/-- Left-edge bits (`ScreenLeft_X_Pos` `$071C`, `ScreenLeft_PageLoc` `$071A`). -/
def gxoL (ram : UInt16 → UInt8) (x : UInt8) : UInt8 :=
  offBits false (ram 0x71C) (ram 0x71A) (objX ram x) (objPage ram x)

/-- `A` on return. -/
def gxoBits (ram : UInt16 → UInt8) (x : UInt8) : UInt8 :=
  bif gxoR ram x != 0 then gxoR ram x else gxoL ram x

/-- `Y` on return: the edge that gave nonzero bits, or `$FF`. -/
def gxoY (ram : UInt16 → UInt8) (x : UInt8) : UInt8 :=
  bif gxoR ram x != 0 then 1 else bif gxoL ram x != 0 then 0 else 0xFF

def gxoCalled (ram : UInt16 → UInt8) (x : UInt8) : Bool :=
  offDiv (ram 0x71D) (ram 0x71B) (objX ram x) (objPage ram x) ||
  (gxoR ram x == 0 && offDiv (ram 0x71C) (ram 0x71A) (objX ram x) (objPage ram x))

/-- Cycles to the RTS (`$F22A`, not executed). -/
def gxoCyc (ram : UInt16 → UInt8) (x : UInt8) : UInt64 :=
  5 + offCyc true (ram 0x71D) (ram 0x71B) (objX ram x) (objPage ram x) +
  (bif gxoR ram x != 0 then 3 else
    8 + offCyc false (ram 0x71C) (ram 0x71A) (objX ram x) (objPage ram x) +
    (bif gxoL ram x != 0 then 3 else 6))

/-- RAM on return: `$04 := X`, `$07` := the last pixel difference, and when `DividePDiff` ran,
`$05 := 8`, `$06 := $38` and its return address on the stack. -/
def gxoRam (x sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  let c := gxoCalled ram x
  bif i == 4 then x
  else bif i == 7 then (bif gxoR ram x != 0 then ram 0x71D - objX ram x else ram 0x71C - objX ram x)
  else bif c && i == 5 then 8
  else bif c && i == 6 then 0x38
  else bif c && i == (0x100 ||| sp.toUInt16) &&& 0x7FF then 0xF2
  else bif c && i == (0x100 ||| (sp + 255).toUInt16) &&& 0x7FF then 0x1D
  else ram i

/-! ## `ScrollHandler` -/

/-- `$AF93`–`$B049`: `ScrollHandler` with its RTS (`$B033`), `X_SubtracterData`,
`OffscrJoypadBitsData`, and `GetScreenPosition`. -/
def scrollCode : List UInt8 :=
  smbPrg% 0xAF93 183

/-- `Player_X_Scroll` after the platform force (`Platform_X_Scroll`, `$03A1`) is added. -/
def scrPxs (ram : UInt16 → UInt8) : UInt8 := ram 0x6FF + ram 0x3A1

/-- Does the screen scroll this frame? -/
def scrolls (ram : UInt16 → UInt8) : Bool :=
  ram 0x723 == 0 && ram 0x755 ≥ 0x50 && ram 0x785 == 0 && (scrPxs ram - 1) &&& 0x80 == 0

/-- `ScrollAmount` when the screen scrolls. -/
def scrAmt (ram : UInt16 → UInt8) : UInt8 :=
  bif ram 0x755 ≥ 0x70 then scrPxs ram else bif scrPxs ram ≥ 2 then scrPxs ram - 1 else scrPxs ram

/-- The screen edges after the scroll (unchanged when the screen does not scroll). -/
def scrLeftX (ram : UInt16 → UInt8) : UInt8 :=
  bif scrolls ram then ram 0x71C + scrAmt ram else ram 0x71C
def scrLeftPage (ram : UInt16 → UInt8) : UInt8 :=
  bif scrolls ram then
    ram 0x71A + (bif (ram 0x71C).toUInt16 + (scrAmt ram).toUInt16 > 0xFF then 1 else 0)
  else ram 0x71A
def scrRightX (ram : UInt16 → UInt8) : UInt8 :=
  bif scrolls ram then scrLeftX ram + 0xFF else ram 0x71D
def scrRightPage (ram : UInt16 → UInt8) : UInt8 :=
  bif scrolls ram then scrLeftPage ram + (bif scrLeftX ram != 0 then 1 else 0) else ram 0x71B

/-- RAM at `ChkPOffscr` (`$B000`), apart from the stack (whose two bytes written here are
overwritten by the next `jsr`). -/
def scrMid (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  let s := scrolls ram
  bif i == 0x6FF then scrPxs ram
  else bif i == 0x775 then (bif s then scrAmt ram else 0)
  else bif s && i == 0x73D then ram 0x73D + scrAmt ram
  else bif s && (i == 0x71C || i == 0x73F) then scrLeftX ram
  else bif s && i == 0x71A then scrLeftPage ram
  else bif s && i == 0 then scrLeftPage ram &&& 1
  else bif s && i == 0x778 then (ram 0x778 &&& 0xFE) ||| (scrLeftPage ram &&& 1)
  else bif s && i == 0x71D then scrRightX ram
  else bif s && i == 0x71B then scrRightPage ram
  else bif s && i == 0x795 then 8
  else ram i

/-- Mario's offscreen bits (`$00` on return). -/
def scrBits (ram : UInt16 → UInt8) : UInt8 := gxoBits (scrMid ram) 0
def clampLeft (ram : UInt16 → UInt8) : Bool := scrBits ram &&& 0x80 != 0
def clampRight (ram : UInt16 → UInt8) : Bool := scrBits ram &&& 0x80 == 0 && scrBits ram &&& 0x20 != 0
def clampX (ram : UInt16 → UInt8) : UInt8 :=
  bif clampLeft ram then scrLeftX ram else scrRightX ram - 0x10
def clampPage (ram : UInt16 → UInt8) : UInt8 :=
  bif clampLeft ram then scrLeftPage ram
  else scrRightPage ram - (bif scrRightX ram < 0x10 then 1 else 0)
/-- `Player_X_Speed := 0`: a clamp, unless the held direction (`Left_Right_Buttons`, `$0C`)
is exactly away from that edge. -/
def stopsSpeed (ram : UInt16 → UInt8) : Bool :=
  (clampLeft ram && ram 0x0C != 1) || (clampRight ram && ram 0x0C != 2)

/-- RAM on return. -/
def scrollRam (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  let c := clampLeft ram || clampRight ram
  bif i == 0x3A1 then 0
  else bif i == 0 then scrBits ram
  else bif c && i == 0x86 then clampX ram
  else bif c && i == 0x6D then clampPage ram
  else bif stopsSpeed ram && i == 0x57 then 0
  else bif i == (0x100 ||| sp.toUInt16) &&& 0x7FF then 0xB0
  else bif i == (0x100 ||| (sp + 255).toUInt16) &&& 0x7FF then 0x04
  else gxoRam 0 (sp + 254) (scrMid ram) i

/-- Cycles from the entry to `ChkPOffscr`. -/
def scrollPreCyc (ram : UInt16 → UInt8) : UInt64 :=
  bif scrolls ram then
    (bif scrPxs ram ≥ 2 then 50 else 49) + (bif ram 0x755 ≥ 0x70 then 12 else 9) + 103
  else bif ram 0x723 != 0 then 27 else bif ram 0x755 < 0x50 then 35 else bif ram 0x785 != 0 then 41
  else 49

/-- Cycles from `GetXOffscreenBits`' return to the RTS (`$B033`, not executed). -/
def scrollPostCyc (ram : UInt16 → UInt8) : UInt64 :=
  bif clampLeft ram then 10 + 29 + (bif ram 0x0C != 1 then 7 else 3) + 6
  else bif clampRight ram then 18 + 29 + (bif ram 0x0C != 2 then 7 else 3) + 6
  else 19 + 6

def scrollCyc (ram : UInt16 → UInt8) : UInt64 :=
  scrollPreCyc ram + 8 + gxoCyc (scrMid ram) 0 + 6 + scrollPostCyc ram


end Smb.Routine
