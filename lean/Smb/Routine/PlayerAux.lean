import Smb.Data.ProofRom
import Smb.Routine.Scroll

/-!
# Mario's per-frame bookkeeping after `ScrollHandler`

`PlayerCtrlRoutine` continues at `$B14F` with

```
jsr GetPlayerOffscreenBits   ; $F180
jsr RelativePlayerPosition   ; $F12A
ldx #$00
jsr BoundingBoxCore          ; $E29C   (Y = 0 here, left by RelativePlayerPosition)
```

```
GetYOffscreenBits ($F239):   like GetXOffscreenBits, for the top edge ($0100) and the bottom
                              edge ($01FF) against Y_HighPos : Y_Position; table YOffscreenBitsData
GetPlayerOffscreenBits:      X := 0; Y := 0; push Y
                              $00 := GetXOffscreenBits >> 4
                              A := GetYOffscreenBits;  $00 := A << 4 | $00
                              pull Y; Player_OffscreenBits ($03D0) := $00; X := ObjectOffset ($08)
RelativePlayerPosition:      X := 0; Y := 0
                              Player_Rel_YPos ($03B8) := Player_Y_Position ($CE)
                              Player_Rel_XPos ($03AD) := Player_X_Position ($86) − ScreenLeft_X_Pos
                              X := ObjectOffset
BoundingBoxCore (X, Y):      $00 := X; $02 := Rel_YPos,y; $01 := Rel_XPos,y; o := 4X (pushed)
                              k := 4 · SprObj_BoundBoxCtrl,x ($0499,x)
                              BoundingBox_UL ($04AC+o) := $01 + BoundBoxCtrlData[k]
                              BoundingBox_LR ($04AE+o) := $01 + BoundBoxCtrlData[k+2]
                              $04AD+o := $02 + BoundBoxCtrlData[k+1];  $04AF+o := $02 + Data[k+3]
                              Y := o; X := $00
```

Each gets a call theorem (closed form at its RTS, exact cycles, flags left unknown except the
I flag) for `sym_run … calls […]`, and a frame lemma: the bytes it may write, and that Mario's
position, speed and vertical state (`$86`, `$6D`, `$0400`, `$57`, `$9F`, `$0433`, `$0416`,
`$CE`, `$B5`, `$1D`) are unchanged. A caller executing the RTS needs the RAM function in its
simp facts (`gyoRam`, `gpoRam`, `gpoMid`, `gxoRam`, `rppRam`, `bbcRam`) to read its return
address.

The only preconditions are on the object offset for `GetYOffscreenBits` (`X < $32`, so
`$B5,x` and `$CE,x` do not wrap onto the scratch bytes `$04`–`$07`) — the other three set or
are given `X = 0` (`BoundingBoxCore` is proved for every `X` and `Y`).
-/
namespace Smb.Routine

/-! ## `GetYOffscreenBits` -/

/-- `$F22B`–`$F233` (`YOffscreenBitsData`), read at a computed index. -/
def yOffscreenBitsData : List UInt8 := smbPrg% 0xF22B 9

/-- `$F234`–`$F26C`: `DefaultYOnscreenOfs`, `HighPosUnitData`, and `GetYOffscreenBits` with
its RTS (`DividePDiff` follows at `$F26D`). -/
def getYOffscreenBitsCode : List UInt8 :=
  smbPrg% 0xF234 57

/-- The offscreen bits for one vertical edge (`top`: `y = 1`, edge `$0100`; else `$01FF`). -/
def offYBits (top : Bool) (ey ehi oy ohi : UInt8) : UInt8 :=
  let d := ey - oy
  let pd := edgePageDiff ey ehi oy ohi
  bif pd &&& 0x80 != 0 then (bif top then 0x00 else 0x0F)
  else bif pd == 0 && d < 0x20 then
    (bif top then ((0x0F : UInt8) <<< ((4 : UInt8) - (d >>> 3))) &&& 0x0F else (0x0F : UInt8) >>> (d >>> 3))
  else (bif top then 0x0F else 0x00)

/-- Cycles of one loop iteration, from `YOfsLoop` to the `cmp #0` after `YLdBData`. -/
def offYCyc (top : Bool) (ey ehi oy ohi : UInt8) : UInt64 :=
  let pd := edgePageDiff ey ehi oy ohi
  bif pd &&& 0x80 != 0 then 37 else bif pd != 0 then 45 else bif ey - oy ≥ 0x20 then 75
  else bif top then 89 else 91

def objY (ram : UInt16 → UInt8) (x : UInt8) : UInt8 := ram ((0xCE + x).toUInt16 &&& 0x7FF)
def objHi (ram : UInt16 → UInt8) (x : UInt8) : UInt8 := ram ((0xB5 + x).toUInt16 &&& 0x7FF)

def gyoT (ram : UInt16 → UInt8) (x : UInt8) : UInt8 := offYBits true 0x00 0x01 (objY ram x) (objHi ram x)
def gyoB (ram : UInt16 → UInt8) (x : UInt8) : UInt8 := offYBits false 0xFF 0x01 (objY ram x) (objHi ram x)

/-- `A` on return. -/
def gyoBits (ram : UInt16 → UInt8) (x : UInt8) : UInt8 :=
  bif gyoT ram x != 0 then gyoT ram x else gyoB ram x

/-- `Y` on return. -/
def gyoY (ram : UInt16 → UInt8) (x : UInt8) : UInt8 :=
  bif gyoT ram x != 0 then 1 else bif gyoB ram x != 0 then 0 else 0xFF

def gyoCalled (ram : UInt16 → UInt8) (x : UInt8) : Bool :=
  offDiv 0x00 0x01 (objY ram x) (objHi ram x) ||
  (gyoT ram x == 0 && offDiv 0xFF 0x01 (objY ram x) (objHi ram x))

/-- Cycles to the RTS (`$F26C`, not executed). -/
def gyoCyc (ram : UInt16 → UInt8) (x : UInt8) : UInt64 :=
  5 + offYCyc true 0x00 0x01 (objY ram x) (objHi ram x) +
  (bif gyoT ram x != 0 then 3 else
    7 + offYCyc false 0xFF 0x01 (objY ram x) (objHi ram x) +
    (bif gyoB ram x != 0 then 3 else 6))

/-- RAM on return: `$04 := X`, `$07` := the last difference, and when `DividePDiff` ran,
`$05 := 4`, `$06 := $20` and its return address (`$F25F`) on the stack. -/
def gyoRam (x sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  let c := gyoCalled ram x
  bif i == 4 then x
  else bif i == 7 then (bif gyoT ram x != 0 then 0x00 - objY ram x else 0xFF - objY ram x)
  else bif c && i == 5 then 4
  else bif c && i == 6 then 0x20
  else bif c && i == (0x100 ||| sp.toUInt16) &&& 0x7FF then 0xF2
  else bif c && i == (0x100 ||| (sp + 255).toUInt16) &&& 0x7FF then 0x5F
  else ram i

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
/-- `hx`: `$B5,x` and `$CE,x` must not wrap around the zero page onto the scratch bytes
`$04`–`$07` written before the second (bottom-edge) iteration reads them again. -/
theorem getYOffscreenBits_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xF239 ≤ a && a ≤ 0xF26C || 0xF26D ≤ a && a ≤ 0xF281) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (htab : CodeAt prg 0x722B yOffscreenBitsData) (hcode : CodeAt prg 0x7234 getYOffscreenBitsCode)
    (hdcode : CodeAt prg 0x726D dividePDiffCode)
    (hI : (p &&& 4 == 0) = false) (hx : x < 0x32) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 75)).run ⟨⟨0xF239, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xF26C, gyoBits ram x, x, gyoY ram x, sp, p'⟩,
        gyoRam x sp ram, prg, cyc + gyoCyc ram x, bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, yOffscreenBitsData, UInt16.reduceAdd] at htab
  simp only [CodeAt, getYOffscreenBitsCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, dividePDiffCode, UInt16.reduceAdd] at hdcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 75)).run ⟨⟨0xF239, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hdcode, hI, hx] until 62060
  all_goals
    intros
    -- `htab` stays: the table is read at a computed index.
    clear hcode hdcode
    subst hrun
    call_finish [gyoRam, gyoCyc, gyoCalled, gyoY, gyoBits, gyoT, gyoB, objY, objHi, offYCyc, offDiv,
      offYBits, edgePageDiff]

/-! ## `GetPlayerOffscreenBits` -/

/-- `$F180`–`$F186`: `GetPlayerOffscreenBits`. -/
def getPlayerOffscreenBitsCode : List UInt8 := smbPrg% 0xF180 7

/-- `$F1C0`–`$F1E2`: `GetOffScreenBitsSet` (RTS at `$F1D6`) and `RunOffscrBitsSubs`. -/
def getOffScreenBitsSetCode : List UInt8 :=
  smbPrg% 0xF1C0 35

/-- `Player_OffscreenBits` (`$03D0`, `$00` and `A`): vertical bits high, horizontal bits low. -/
def gpoBits (ram : UInt16 → UInt8) : UInt8 := (gyoBits ram 0 <<< 4) ||| (gxoBits ram 0 >>> 4)

/-- RAM when `GetYOffscreenBits` starts: `$00`, the pushed `Y` and two return addresses, and
`GetXOffscreenBits`' writes. -/
def gpoMid (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  bif i == 0 then gxoBits ram 0 >>> 4
  else bif i == (0x100 ||| sp.toUInt16) &&& 0x7FF then 0
  else bif i == (0x100 ||| (sp + 255).toUInt16) &&& 0x7FF then 0xF1
  else bif i == (0x100 ||| (sp + 254).toUInt16) &&& 0x7FF then 0xC4
  else bif i == (0x100 ||| (sp + 253).toUInt16) &&& 0x7FF then 0xF1
  else bif i == (0x100 ||| (sp + 252).toUInt16) &&& 0x7FF then 0xD9
  else gxoRam 0 (sp + 251) ram i

def gpoRam (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  bif i == 0 || i == 0x3D0 then gpoBits ram
  else gyoRam 0 (sp + 253) (gpoMid sp ram) i

def gpoCyc (ram : UInt16 → UInt8) : UInt64 := 81 + gxoCyc ram 0 + gyoCyc ram 0

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
theorem getPlayerOffscreenBits_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xF180 ≤ a && a ≤ 0xF186 || 0xF1C0 ≤ a && a ≤ 0xF1E2 ||
      0xF1F6 ≤ a && a ≤ 0xF22A || 0xF239 ≤ a && a ≤ 0xF281) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x7180 getPlayerOffscreenBitsCode)
    (hscode : CodeAt prg 0x71C0 getOffScreenBitsSetCode)
    (hxtab : CodeAt prg 0x71E3 xOffscreenBitsData) (hxcode : CodeAt prg 0x71F3 getXOffscreenBitsCode)
    (hytab : CodeAt prg 0x722B yOffscreenBitsData) (hycode : CodeAt prg 0x7234 getYOffscreenBitsCode)
    (hdcode : CodeAt prg 0x726D dividePDiffCode)
    (hI : (p &&& 4 == 0) = false) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 200)).run ⟨⟨0xF180, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xF1D6, gpoBits ram, ram 8, 0, sp, p'⟩,
        gpoRam sp ram, prg, cyc + gpoCyc ram, bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, getPlayerOffscreenBitsCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, getOffScreenBitsSetCode, UInt16.reduceAdd] at hscode
  -- The callees' RTS bytes, executed here after their call theorems.
  have hr1 : prg 0x722A = 0x60 := by
    have h := hxcode; simp only [CodeAt, getXOffscreenBitsCode, UInt16.reduceAdd] at h; simp [h]
  have hr2 : prg 0x726C = 0x60 := by
    have h := hycode; simp only [CodeAt, getYOffscreenBitsCode, UInt16.reduceAdd] at h; simp [h]
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 200)).run ⟨⟨0xF180, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hscode, hr1, hr2, hI, gxoRam, gyoRam] until 61910
    calls [getXOffscreenBits_call, getYOffscreenBits_call]
  all_goals
    intros
    clear hcode hscode hr1 hr2 hxtab hxcode hytab hycode hdcode
    subst hrun
    (try simp only [gxoBits, gxoY, gxoR, gxoL, objX, objPage, offBits, gyoBits, gyoY, gyoT, gyoB,
      objY, objHi, offYBits, edgePageDiff] at *)
    call_finish [gpoRam, gpoMid, gpoBits, gpoCyc, gxoRam, gxoCyc, gxoCalled, gxoY, gxoBits, gxoL, gxoR,
      objX, objPage, offCyc, offDiv, offBits, gyoRam, gyoCyc, gyoCalled, gyoY, gyoBits, gyoT, gyoB,
      objY, objHi, offYCyc, offYBits, edgePageDiff]

/-! ## `RelativePlayerPosition` -/

/-- `$F12A`–`$F130`: `RelativePlayerPosition`. -/
def relativePlayerPositionCode : List UInt8 := smbPrg% 0xF12A 7

/-- `$F142`–`$F147`: `RelWOfs` with its RTS. -/
def relWOfsCode : List UInt8 := smbPrg% 0xF142 6

/-- `$F171`–`$F17F`: `GetObjRelativePosition` with its RTS. -/
def getObjRelativePositionCode : List UInt8 :=
  smbPrg% 0xF171 15

/-- `Player_Rel_XPos`: Mario's X on screen. -/
def relX (ram : UInt16 → UInt8) : UInt8 := ram 0x86 - ram 0x71C

def rppRam (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  bif i == 0x3B8 then ram 0xCE
  else bif i == 0x3AD then relX ram
  else bif i == (0x100 ||| sp.toUInt16) &&& 0x7FF then 0xF1
  else bif i == (0x100 ||| (sp + 255).toUInt16) &&& 0x7FF then 0x44
  else ram i

set_option maxHeartbeats 40000000 in
theorem relativePlayerPosition_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xF12A ≤ a && a ≤ 0xF130 || 0xF142 ≤ a && a ≤ 0xF147 ||
      0xF171 ≤ a && a ≤ 0xF17F) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x712A relativePlayerPositionCode) (hwcode : CodeAt prg 0x7142 relWOfsCode)
    (hgcode : CodeAt prg 0x7171 getObjRelativePositionCode)
    (hI : (p &&& 4 == 0) = false) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 20)).run ⟨⟨0xF12A, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xF147, relX ram, ram 8, 0, sp, p'⟩,
        rppRam sp ram, prg, cyc + 46, bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, relativePlayerPositionCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, relWOfsCode, UInt16.reduceAdd] at hwcode
  simp only [CodeAt, getObjRelativePositionCode, UInt16.reduceAdd] at hgcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 20)).run ⟨⟨0xF12A, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hwcode, hgcode, hI] until 61767
  all_goals
    intros
    clear hcode hwcode hgcode
    subst hrun
    call_finish [rppRam, relX]

/-! ## `BoundingBoxCore` -/

/-- `$E29C`–`$E2DD`: `BoundingBoxCore` with its RTS. -/
def boundingBoxCoreCode : List UInt8 :=
  smbPrg% 0xE29C 66

/-- RAM address `base + i` (absolute indexed). -/
def absIdx (base : UInt16) (i : UInt8) : UInt16 := (base + i.toUInt16) &&& 0x7FF
/-- One cycle more when `base + i` crosses a page. -/
def pageX (base : UInt16) (i : UInt8) : UInt64 :=
  bif (base + i.toUInt16 ^^^ base) &&& 0xFF00 != 0 then 1 else 0
/-- `BoundBoxCtrlData` (`$E1FD`), read at a computed index (left as ROM bytes). -/
def bbData (prg : UInt16 → UInt8) (base : UInt16) (i : UInt8) : UInt8 := prg ((base + i.toUInt16) &&& 0x7FFF)

/-- `4 · SprObj_BoundBoxCtrl,x`: the object's row of `BoundBoxCtrlData`. -/
def bbcRow (ram : UInt16 → UInt8) (x : UInt8) : UInt8 := ram (absIdx 0x499 x) <<< 2

def bbcRam (x y sp : UInt8) (prg ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  let ry := ram (absIdx 0x3B8 y)
  let rx := ram (absIdx 0x3AD y)
  let o := x <<< 2
  let k := bbcRow ram x
  bif i == 0 then x
  else bif i == 2 then ry
  else bif i == 1 then rx
  else bif i == (0x100 ||| sp.toUInt16) &&& 0x7FF then o
  else bif i == absIdx 0x4AC o then rx + bbData prg 0xE1FD k
  else bif i == absIdx 0x4AE o then rx + bbData prg 0xE1FF k
  else bif i == absIdx 0x4AC (o + 1) then ry + bbData prg 0xE1FD (k + 1)
  else bif i == absIdx 0x4AE (o + 1) then ry + bbData prg 0xE1FF (k + 1)
  else ram i

def bbcCyc (x y : UInt8) (ram : UInt16 → UInt8) : UInt64 :=
  let k := bbcRow ram x
  107 + pageX 0x3B8 y + pageX 0x3AD y + pageX 0x499 x + pageX 0xE1FD k + pageX 0xE1FF k +
    pageX 0xE1FD (k + 1) + pageX 0xE1FF (k + 1)

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
/-- For every `X` and `Y`; `PlayerCtrlRoutine` calls it with `X = 0`, `Y = 0`
(`boundingBoxCore_call_player`). -/
theorem boundingBoxCore_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xE29C ≤ a && a ≤ 0xE2DD) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x629C boundingBoxCoreCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xE29C, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xE2DD, x <<< 2, x, x <<< 2, sp, p'⟩,
        bbcRam x y sp prg ram, prg, cyc + bbcCyc x y ram, bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, boundingBoxCoreCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xE29C, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI] until 58077
  all_goals
    intros
    clear hcode
    subst hrun
    call_finish [bbcRam, bbcCyc, bbcRow, absIdx, pageX, bbData]

/-- The call in `PlayerCtrlRoutine` (`$B157`): `X = 0` (`ldx #$00`), `Y = 0` (left by
`RelativePlayerPosition`). -/
theorem boundingBoxCore_call_player (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xE29C ≤ a && a ≤ 0xE2DD) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x629C boundingBoxCoreCode) (hI : (p &&& 4 == 0) = false)
    (hx : x = 0) (hy : y = 0) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xE29C, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xE2DD, 0, 0, 0, sp, p'⟩,
        bbcRam 0 0 sp prg ram, prg, cyc + bbcCyc 0 0 ram, bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  subst hx hy
  exact boundingBoxCore_call stop hstop m a 0 0 sp p ram prg cyc bad hcode hI

/-! ## What they change -/

/-- Mario's position, speed and vertical state. -/
def marioBytes : List UInt16 := [0x86, 0x6D, 0x400, 0x57, 0x9F, 0x433, 0x416, 0xCE, 0xB5, 0x1D]

/-- `r` agrees with `ram` on Mario's bytes. -/
def marioSame (r ram : UInt16 → UInt8) : Prop := ∀ i ∈ marioBytes, r i = ram i

theorem marioSame_of (r ram : UInt16 → UInt8) (h : ∀ i : UInt16, i ∈ marioBytes → r i = ram i) :
    marioSame r ram := h

set_option maxRecDepth 20000 in
/-- `GetPlayerOffscreenBits` writes only `$00`, `$03D0`, `$04`–`$07` and the six stack bytes
below `sp`. -/
theorem gpoRam_frame (sp : UInt8) (ram : UInt16 → UInt8) :
    (∀ i : UInt16, i ≠ 0 → i ≠ 0x3D0 → i ≠ 4 → i ≠ 5 → i ≠ 6 → i ≠ 7 →
      (∀ k : UInt8, k ∈ [0, 255, 254, 253, 252, 251, 250] → i ≠ (0x100 ||| (sp + k).toUInt16) &&& 0x7FF) →
      gpoRam sp ram i = ram i) ∧ marioSame (gpoRam sp ram) ram := by
  have h : ∀ i : UInt16, i ≠ 0 → i ≠ 0x3D0 → i ≠ 4 → i ≠ 5 → i ≠ 6 → i ≠ 7 →
      (∀ k : UInt8, k ∈ [0, 255, 254, 253, 252, 251, 250] → i ≠ (0x100 ||| (sp + k).toUInt16) &&& 0x7FF) →
      gpoRam sp ram i = ram i := by
    intro i h0 h1 h4 h5 h6 h7 hs
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
    obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := hs
    simp only [gpoRam, gpoMid, gyoRam, gxoRam, bne]
    generalize gpoBits ram = b
    generalize gyoCalled _ _ = c1
    generalize gxoCalled _ _ = c2
    revert s0
    simp only [UInt8.add_zero]
    intro s0
    bv_decide
  refine ⟨h, fun i hi => ?_⟩
  simp only [marioBytes, List.mem_cons, List.not_mem_nil, or_false] at hi
  apply h <;> (try intro k hk) <;> (try simp only [List.mem_cons, List.not_mem_nil, or_false] at hk) <;>
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try decide) <;> (try (rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> bv_decide))

/-- `RelativePlayerPosition` writes only `$03B8`, `$03AD` and two stack bytes. -/
theorem rppRam_frame (sp : UInt8) (ram : UInt16 → UInt8) :
    (∀ i : UInt16, i ≠ 0x3B8 → i ≠ 0x3AD → i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF →
      i ≠ (0x100 ||| (sp + 255).toUInt16) &&& 0x7FF → rppRam sp ram i = ram i) ∧
    marioSame (rppRam sp ram) ram := by
  have h : ∀ i : UInt16, i ≠ 0x3B8 → i ≠ 0x3AD → i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF →
      i ≠ (0x100 ||| (sp + 255).toUInt16) &&& 0x7FF → rppRam sp ram i = ram i := by
    intro i h1 h2 h3 h4
    simp only [rppRam]
    generalize relX ram = r
    bv_decide
  refine ⟨h, fun i hi => ?_⟩
  simp only [marioBytes, List.mem_cons, List.not_mem_nil, or_false] at hi
  apply h <;> rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | decide | bv_decide

/-- `BoundingBoxCore` writes only `$00`–`$02`, one stack byte, and the object's bounding box
(`$04AC + 4X` … `$04AF + 4X`). -/
theorem bbcRam_frame (x y sp : UInt8) (prg ram : UInt16 → UInt8) :
    (∀ i : UInt16, i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF →
      i ≠ absIdx 0x4AC (x <<< 2) → i ≠ absIdx 0x4AD (x <<< 2) → i ≠ absIdx 0x4AE (x <<< 2) →
      i ≠ absIdx 0x4AF (x <<< 2) → bbcRam x y sp prg ram i = ram i) ∧
    marioSame (bbcRam x y sp prg ram) ram := by
  have h : ∀ i : UInt16, i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF →
      i ≠ absIdx 0x4AC (x <<< 2) → i ≠ absIdx 0x4AD (x <<< 2) → i ≠ absIdx 0x4AE (x <<< 2) →
      i ≠ absIdx 0x4AF (x <<< 2) → bbcRam x y sp prg ram i = ram i := by
    intro i h0 h1 h2 h3 h4 h5 h6 h7
    simp only [bbcRam, absIdx] at *
    generalize bbcRow ram x = k
    generalize ram ((0x3B8 + y.toUInt16) &&& 0x7FF) = ry
    generalize ram ((0x3AD + y.toUInt16) &&& 0x7FF) = rx
    generalize bbData prg 0xE1FD k = d0
    generalize bbData prg 0xE1FF k = d1
    generalize bbData prg 0xE1FD (k + 1) = d2
    generalize bbData prg 0xE1FF (k + 1) = d3
    bv_decide
  refine ⟨h, fun i hi => ?_⟩
  simp only [marioBytes, List.mem_cons, List.not_mem_nil, or_false] at hi
  apply h <;> rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try simp only [absIdx]) <;> first | decide | bv_decide

end Smb.Routine
