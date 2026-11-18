import Smb.Cpu

/-
Executable NROM NES model for SMB. C and Lean share the same explicitly selected
NTSC clock phase: bus access after one PPU dot, NMI sampling after the second,
then the third dot. Vblank and pre-render flags change at dot 1; NMI is an edge
of vblank AND PPUCTRL.7, sampled separately from instruction interrupt polling.

The PPU still evaluates stable scanlines without producing pixels. Unsupported
rendering changes, APU reads/DMC, IRQ enable, and unsupported opcodes set a sticky
flag. Passing the guards is not a hardware-equivalence proof. See docs/model.md.
-/
namespace Smb

/-- Sentinel for "no event / no position". -/
def NONE : UInt32 := 0xFFFFFFFF

structure NES where
  -- cartridge (never written)
  prg : ByteArray
  chr : ByteArray
  vertical : Bool
  -- CPU
  pc : UInt16
  a : UInt8
  x : UInt8
  y : UInt8
  s : UInt8
  p : UInt8
  ram : ByteArray
  -- PPU registers and memory
  ctrl : UInt8
  mask : UInt8
  oamaddr : UInt8
  w : Bool
  fx : UInt8
  rbuf : UInt8
  vbl : Bool
  spr0 : Bool
  ovf : Bool
  iolatch : UInt8
  v : UInt16
  t : UInt16
  ntram : ByteArray
  pal : ByteArray
  oam : ByteArray
  -- PPU timing: dot position in the current frame (frame starts at scanline 240, dot 0)
  fpos : UInt32
  flen : UInt32
  overflowPos : UInt32
  hitPos : UInt32
  line : UInt32
  sp0x : UInt16
  sp0data : UInt8
  nextEv : UInt32
  evIdx : UInt8
  odd : UInt32
  dead : UInt8
  nmiPending : Bool
  frameDone : Bool
  skipped : UInt32
  suppressVbl : Bool
  nmiLine : Bool
  nmiPolled : Bool
  dmaPending : Bool
  dmaPage : UInt8
  -- controllers
  pad0 : UInt8
  pad1 : UInt8
  sh0 : UInt8
  sh1 : UInt8
  strobe : Bool
  -- bookkeeping
  bus : UInt8
  padRead : UInt8
  padBit : UInt8
  ioLow : UInt64
  ioBit5 : UInt64
  ioHigh : UInt64
  polls : UInt32
  unmodelled : Bool
  cyc : UInt64

namespace NES

/-! ### Linear updates of the byte arrays

Taking the array out of the structure before updating it keeps its reference count at one,
so `set!` updates in place instead of copying. -/

@[inline] def setRam (s : NES) (i : Nat) (b : UInt8) : NES :=
  let arr := s.ram
  let s := { s with ram := ByteArray.empty }
  { s with ram := arr.set! i b }

@[inline] def setNt (s : NES) (i : Nat) (b : UInt8) : NES :=
  let arr := s.ntram
  let s := { s with ntram := ByteArray.empty }
  { s with ntram := arr.set! i b }

@[inline] def setPal (s : NES) (i : Nat) (b : UInt8) : NES :=
  let arr := s.pal
  let s := { s with pal := ByteArray.empty }
  { s with pal := arr.set! i b }

@[inline] def setOam (s : NES) (i : Nat) (b : UInt8) : NES :=
  let arr := s.oam
  let s := { s with oam := ByteArray.empty }
  { s with oam := arr.set! i b }

@[inline] def chrAt (s : NES) (a : UInt16) : UInt8 := s.chr.get! (a &&& 0x1FFF).toNat
@[inline] def prgAt (s : NES) (a : UInt16) : UInt8 := s.prg.get! (a &&& 0x7FFF).toNat
@[inline] def ntIndex (s : NES) (a : UInt16) : Nat :=
  let i : UInt16 := if s.vertical then a &&& (0x7FF : UInt16) else (a &&& (0x3FF : UInt16)) ||| ((a >>> (1 : UInt16)) &&& (0x400 : UInt16))
  i.toNat
@[inline] def ntRead (s : NES) (a : UInt16) : UInt8 := s.ntram.get! (s.ntIndex a)

/-! ### PPU events -/

def line0 (s : NES) : UInt32 := 22 * 341 - s.skipped

/-- Event positions: vblank, clear flags, pre-render copy, odd-frame skip,
line start, sprite status changes, line end, frame end. -/
def phPos (s : NES) (ph : UInt8) : UInt32 :=
  match ph with
  | 0 => 342
  | 1 => 21 * 341 + 1
  | 2 => 21 * 341 + 304
  | 3 => 21 * 341 + 339
  | 4 => line0 s + s.line * 341
  | 5 => NONE -- sprite status events are merged independently by sched
  | 6 => line0 s + s.line * 341 + 256
  | 7 => s.flen
  | _ => NONE

/-- Advance `evIdx` to the next event that happens this frame and record its position. -/
def sched (s : NES) : NES :=
  let s := go 9 s
  { s with nextEv := min s.nextEv (min s.hitPos s.overflowPos) }
where
  go : Nat → NES → NES
    | 0, s => { s with nextEv := 0x7fffffff }
    | n + 1, s =>
      if s.evIdx ≥ 8 then { s with nextEv := 0x7fffffff }
      else
        let pos := phPos s s.evIdx
        if pos != NONE then { s with nextEv := pos } else go n { s with evIdx := s.evIdx + 1 }

def incY (v : UInt16) : UInt16 :=
  if v &&& 0x7000 != 0x7000 then v + 0x1000
  else
    let v : UInt16 := v &&& ~~~(0x7000 : UInt16)
    let y : UInt16 := (v &&& 0x03E0) >>> 5
    let (y, v) : UInt16 × UInt16 :=
      if y == 29 then (0, v ^^^ 0x0800) else if y == 31 then (0, v) else (y + 1, v)
    (v &&& ~~~(0x03E0 : UInt16)) ||| (y <<< 5)

def bgOpaque (s : NES) (v : UInt16) (px : UInt32) : Bool :=
  let fine := s.fx.toUInt32 + px
  let cx0 := (v &&& 31).toUInt32 + (fine >>> 3)
  let nt0 := v &&& 0x0C00
  let (cx, nt) := if cx0 ≥ 32 then (cx0 - 32, nt0 ^^^ 0x0400) else (cx0, nt0)
  let cy := (v >>> 5) &&& 31
  let fy := (v >>> 12) &&& 7
  let addr : UInt16 := (0x2000 : UInt16) ||| nt ||| (cy <<< 5) ||| cx.toUInt16
  let tile := s.ntRead addr
  let pa : UInt16 := (if s.ctrl &&& 0x10 != 0 then 0x1000 else 0) + tile.toUInt16 * 16 + fy
  let bit := (7 - (fine &&& 7)).toUInt8
  ((s.chrAt pa >>> bit) ||| (s.chrAt (pa + 8) >>> bit)) &&& 1 != 0

def reverseBits (d : UInt8) : UInt8 :=
  (List.range 8).foldl (fun (r : UInt8) i =>
    if d &&& ((1 : UInt8) <<< i.toUInt8) != 0 then r ||| ((0x80 : UInt8) >>> i.toUInt8) else r) 0

/-- Sprite-0 pixels for the line after `line`, as fetched at the end of `line`. -/
def fetchSprite0 (s : NES) : NES :=
  let h : UInt32 := if s.ctrl &&& 0x20 != 0 then 16 else 8
  let oy := (s.oam.get! 0).toUInt32
  if s.line < oy || s.line - oy ≥ h then { s with sp0x := 0x100 }
  else
    let t := s.line - oy
    let tile := s.oam.get! 1
    let attr := s.oam.get! 2
    let row := if attr &&& 0x80 != 0 then h - 1 - t else t
    let pa : UInt32 :=
      if h == 8 then (if s.ctrl &&& 0x08 != 0 then 0x1000 else 0) + tile.toUInt32 * 16 + row
      else (if tile &&& 1 != 0 then 0x1000 else 0) + (tile &&& 0xFE).toUInt32 * 16
        + (if row ≥ 8 then 16 else 0) + (row &&& 7)
    let d := s.chrAt pa.toUInt16 ||| s.chrAt (pa + 8).toUInt16
    let d := if attr &&& 0x40 != 0 then reverseBits d else d
    { s with sp0x := (s.oam.get! 3).toUInt16, sp0data := d }

/-- CPU-visible sprite-zero status time, or `NONE`. The selected phase observes
the delayed output at X + 4 (pixel collision plus the PPU status pipeline). -/
def lineHit (s : NES) (firstX : UInt32 := 0) : UInt32 :=
  if s.sp0x == 0x100 || s.mask &&& 0x18 != 0x18 || s.spr0 then NONE
  else
    let hit := (List.range 8).findSome? fun i =>
      let x := s.sp0x.toUInt32 + i.toUInt32
      if x ≥ firstX && x < 255 && (x ≥ 8 || s.mask &&& 6 == 6) &&
          s.sp0data &&& ((0x80 : UInt8) >>> i.toUInt8) != 0 && s.bgOpaque s.v x then
        some (line0 s + s.line * 341 + x + 4)
      else none
    hit.getD NONE

/-- First sprite overflow time, including the diagonal scan after eight sprites.
OAM and sprite size must stay stable during evaluation; writes are guarded. -/
def spriteOverflow (s : NES) : UInt32 :=
  if s.ovf || s.mask &&& 0x18 == 0 then NONE else go 64 0 0 0 66
where
  go : Nat → Nat → Nat → Nat → UInt32 → UInt32
    | 0, _, _, _, _ => NONE
    | n + 1, i, m, count, dot =>
      if dot > 256 then NONE else
      let y := (s.oam.get! (4 * i + m)).toUInt32
      let h : UInt32 := if s.ctrl &&& 0x20 != 0 then 16 else 8
      let inRange := s.line ≥ y && s.line - y < h
      if count == 8 then
        if inRange then line0 s + s.line * 341 + dot + 1
        else go n (i + 1) ((m + 1) % 4) count (dot + 2)
      else go n (i + 1) m (count + if inRange then 1 else 0) (dot + if inRange then 8 else 2)

/-- Handle the event at `evIdx` (whose position has been reached) and schedule the next. -/
def handleEv (s : NES) : NES :=
  if s.hitPos == s.nextEv then sched { s with spr0 := true, hitPos := NONE }
  else if s.overflowPos == s.nextEv then sched { s with ovf := true, overflowPos := NONE }
  else match s.evIdx with
  | 0 => sched { s with vbl := !s.suppressVbl, suppressVbl := false, evIdx := 1 }
  | 1 => sched { s with vbl := false, spr0 := false, ovf := false, dead := 0, evIdx := 2 }
  | 2 =>
    let s := { s with unmodelled := s.unmodelled || (s.mask &&& 0x18 != 0 && s.oamaddr ≥ 8) }
    sched { s with oamaddr := (if s.mask &&& 0x18 != 0 then 0 else s.oamaddr),
                   v := (if s.mask &&& 0x18 != 0 then s.t else s.v), sp0x := 0x100, line := 0, evIdx := 3 }
  | 3 =>
    let skipped : UInt32 := if s.odd != 0 && s.mask &&& 0x18 != 0 then 1 else 0
    sched { s with skipped, flen := 262 * 341 - skipped, evIdx := 4 }
  | 4 => sched { s with hitPos := lineHit s, overflowPos := spriteOverflow s, evIdx := 5 }
  | 6 =>
    let s :=
      if s.mask &&& 0x18 != 0 then
        let s := fetchSprite0 { s with v := incY s.v }
        { s with oamaddr := 0, v := (s.v &&& 0xFBE0) ||| (s.t &&& 0x041F) }
      else { s with sp0x := 0x100 }
    let s := { s with line := s.line + 1 }
    if s.line < (240 : UInt32) then sched { s with evIdx := 4 } else sched { s with evIdx := 7 }
  | 7 =>
    sched { s with frameDone := true, fpos := s.fpos - s.flen, odd := s.odd ^^^ 1,
                   skipped := 0, flen := 262 * 341, hitPos := NONE, overflowPos := NONE, evIdx := 0 }
  | _ => s

def ppuEvents (s : NES) : NES := go 64 s
where
  go : Nat → NES → NES
    | 0, s => { s with unmodelled := true }
    | n + 1, s => if s.fpos ≥ s.nextEv then go n (handleEv s) else s

@[inline] def advancePpu (s : NES) (dots : UInt32) : NES :=
  let s := { s with fpos := s.fpos + dots }
  if s.fpos ≥ s.nextEv then ppuEvents s else s

@[inline] def beginCycle (s : NES) : NES :=
  let s := { s with cyc := s.cyc + 1 }
  let s := if s.cyc &&& 1 == 0 && s.strobe then { s with sh0 := s.pad0, sh1 := s.pad1 } else s
  advancePpu s 1

@[inline] def endCycle (s : NES) : NES :=
  let s := advancePpu s 1
  let line := s.vbl && s.ctrl &&& 0x80 != 0
  advancePpu { s with
    nmiPolled := s.nmiPending, nmiPending := s.nmiPending || (line && !s.nmiLine), nmiLine := line } 1

@[inline] def tickS (s : NES) : NES := endCycle (beginCycle s)

/-! ### PPU registers -/

def ppuMemRead (s : NES) (a : UInt16) : UInt8 :=
  let a := a &&& 0x3FFF
  if a < 0x2000 then s.chrAt a
  else if a < 0x3F00 then s.ntRead a
  else
    let a := a &&& 0x1F
    let a := if a &&& 0x13 == 0x10 then a &&& 0x0F else a
    s.pal.get! a.toNat

def ppuMemWrite (s : NES) (a : UInt16) (b : UInt8) : NES :=
  let a := a &&& 0x3FFF
  if a < 0x2000 then s
  else if a < 0x3F00 then s.setNt (s.ntIndex a) b
  else
    let a := a &&& 0x1F
    let a := if a &&& 0x13 == 0x10 then a &&& 0x0F else a
    s.setPal a.toNat (b &&& 0x3F)

@[inline] def vramInc (s : NES) : UInt16 := if s.ctrl &&& 4 != 0 then 32 else 1

def rendering (s : NES) : Bool :=
  s.dead == 0 && s.mask &&& 0x18 != 0 && s.fpos ≥ 21 * 341

/-- A deterministic twenty-frame approximation to analogue PPU bus decay.
Only groups actually driven by a read refresh their timestamps. -/
def ioDecay (s : NES) : NES :=
  let v := if s.cyc - s.ioLow ≥ 600000 then s.iolatch &&& 0xE0 else s.iolatch
  let v := if s.cyc - s.ioBit5 ≥ 600000 then v &&& 0xDF else v
  let v := if s.cyc - s.ioHigh ≥ 600000 then v &&& 0x3F else v
  { s with iolatch := v }

def ppuRegRead (s : NES) (a : UInt16) : UInt8 × NES :=
  let s := ioDecay s
  let (r, s) : UInt8 × NES :=
    match a &&& 7 with
    | 2 =>
      let r := (if s.vbl then 0x80 else 0) ||| (if s.spr0 then 0x40 else 0)
        ||| (if s.ovf then 0x20 else 0) ||| (s.iolatch &&& 0x1F)
      (r, { s with vbl := false, w := false, suppressVbl := s.suppressVbl || s.fpos == 341,
                   ioBit5 := s.cyc, ioHigh := s.cyc })
    | 4 => (s.oam.get! s.oamaddr.toNat, { s with
                unmodelled := s.unmodelled || rendering s, ioLow := s.cyc, ioBit5 := s.cyc, ioHigh := s.cyc })
    | 7 =>
      let s := { s with unmodelled := s.unmodelled || rendering s }
      let addr := s.v &&& 0x3FFF
      let palette := (ppuMemRead s addr &&& (if s.mask &&& 1 != 0 then 0x30 else 0x3F)) ||| (s.iolatch &&& 0xC0)
      let (r, rbuf) := if addr < 0x3F00 then (s.rbuf, ppuMemRead s addr) else (palette, s.ntRead addr)
      (r, { s with
            rbuf, v := (s.v + vramInc s) &&& 0x7FFF, ioLow := s.cyc, ioBit5 := s.cyc, ioHigh := if addr < 0x3F00 then s.cyc else s.ioHigh })
    | _ => (s.iolatch, s)
  (r, { s with iolatch := r })

def ppuRegWrite (s : NES) (a : UInt16) (b : UInt8) : NES :=
  let reg := a &&& 7
  let s := { s with iolatch := b, ioLow := s.cyc, ioBit5 := s.cyc, ioHigh := s.cyc }
  if s.dead != 0 && (reg == 0 || reg == 1 || reg == 5 || reg == 6) then s else
  let oldRender := s.mask &&& 0x18 != 0
  let newRender := b &&& 0x18 != 0
  let start := line0 s + s.line * 341
  let earlyEnable := !oldRender && newRender && s.line < 240 && s.fpos ≥ start &&
    s.fpos - start ≤ 60 && s.sp0x == 0x100 && s.oamaddr == 0
  -- A later enable, in a long NMI: evaluation on this line is only partial, which can't matter if
  -- sprite 0 isn't in range and no overflow is possible. It has to stay clear of dots 256 and 257.
  let oy := (s.oam.get! 0).toUInt32
  let h : UInt32 := if s.ctrl &&& 0x20 != 0 then 16 else 8
  let lateEnable := !oldRender && newRender && s.sp0x == 0x100 && s.oamaddr == 0 && s.fpos ≥ line0 s &&
    (s.line ≥ 240 || (!(s.line ≥ oy && s.line - oy < h) &&
      !(s.fpos ≥ start + 251 && s.fpos ≤ start + 257) && spriteOverflow { s with mask := b } == NONE))
  let unsupported :=
    (s.dead == 0 && s.fpos ≥ 21 * 341 + 257 && reg == 1 && oldRender != newRender && !earlyEnable && !lateEnable) ||
    (rendering s && (reg == 3 || reg == 4 || reg == 7 ||
    (reg == 0 && (s.ctrl ^^^ b) &&& 0x38 != 0) ||
    (!s.spr0 && s.fpos ≥ line0 s &&
      ((reg == 5 && !s.w && b &&& 7 != s.fx) ||
       (reg == 6 && s.w && ((s.t &&& 0xFF00) ||| b.toUInt16) != s.v)))))
  let s := { s with unmodelled := s.unmodelled || unsupported }
  let s := { s with iolatch := b }
  let reg : UInt16 := a &&& 7
  if reg == 0 then
    let nt : UInt16 := (b &&& 3).toUInt16
    let t : UInt16 := (s.t &&& (0xF3FF : UInt16)) ||| (nt <<< (10 : UInt16))
    { s with ctrl := b, t }
  else if reg == 1 then
    let s := { s with mask := b }
    let s := if earlyEnable then { s with overflowPos := spriteOverflow s } else s
    if s.evIdx == 5 || s.evIdx == 6 then
      let firstX := if s.fpos ≥ start then s.fpos - start else 0
      let hit := if s.hitPos != NONE && s.hitPos ≤ s.fpos + 3 then s.hitPos else lineHit s firstX
      sched { s with hitPos := hit, evIdx := 5 }
    else s
  else if reg == 3 then { s with oamaddr := b }
  else if reg == 4 then
    let i := s.oamaddr
    { s.setOam i.toNat (if i &&& 3 == 2 then b &&& 0xE3 else b) with oamaddr := i + 1 }
  else if reg == 5 then
    if !s.w then
      let hi : UInt16 := (b >>> 3).toUInt16
      { s with t := (s.t &&& (0xFFE0 : UInt16)) ||| hi, fx := b &&& 7, w := true }
    else
      let fy : UInt16 := (b &&& 7).toUInt16
      let cy : UInt16 := (b &&& 0xF8).toUInt16
      { s with t := (s.t &&& (0x8C1F : UInt16)) ||| (fy <<< (12 : UInt16)) ||| (cy <<< (2 : UInt16)), w := false }
  else if reg == 6 then
    if !s.w then
      let hi : UInt16 := (b &&& 0x3F).toUInt16
      { s with t := (s.t &&& (0x00FF : UInt16)) ||| (hi <<< (8 : UInt16)), w := true }
    else
      let t : UInt16 := (s.t &&& (0xFF00 : UInt16)) ||| b.toUInt16
      { s with t, v := t, w := false }
  else if reg == 7 then
    let v := s.v
    let inc := vramInc s
    { ppuMemWrite s v b with v := (v + inc) &&& 0x7FFF }
  else s

/-! ### Bus -/

/-- A single read cycle, without recursively starting DMA. -/
def readCycle (s : NES) (a : UInt16) : UInt8 × NES :=
  let s := beginCycle s
  let (r, s) : UInt8 × NES :=
    if a < 0x2000 then (s.ram.get! (a &&& 0x7FF).toNat, s)
    else if a < 0x4000 then ppuRegRead s a
    else if a == 0x4016 || a == 0x4017 then
      let port : UInt8 := if a == 0x4016 then 1 else 2
      let pad := if port == 1 then s.pad0 else s.pad1
      let sh := if port == 1 then s.sh0 else s.sh1
      let bit := if s.strobe then pad &&& 1 else if s.padRead == port then s.padBit else sh &&& 1
      let shift := !s.strobe && s.padRead != port
      (s.bus &&& 0xE0 ||| bit, { s with
        padBit := bit, sh0 := if shift && port == 1 then (sh >>> 1) ||| 0x80 else s.sh0,
        sh1 := if shift && port == 2 then (sh >>> 1) ||| 0x80 else s.sh1 })
    else if a ≥ 0x8000 then (s.prgAt a, s)
    else (s.bus, { s with unmodelled := s.unmodelled || a == 0x4015 })
  let s := endCycle { s with bus := r, padRead := if a == 0x4016 then 1 else if a == 0x4017 then 2 else 0 }
  if a ≥ 0x2000 && a < 0x4000 && a &&& 7 == 2 then
    -- Vblank is latched at the beginning; the sprite flags at the end of the read.
    let r := (r &&& 0x9F) ||| (if s.spr0 then 0x40 else 0) ||| (if s.ovf then 0x20 else 0)
    (r, { s with bus := r, iolatch := r })
  else (r, s)

/-- DMA halts the next read, aligns to a get cycle, then performs 256 pairs.
Consecutive writes to $4014 replace the pending page before any DMA can start. -/
def oamDma (s : NES) (haltAddr : UInt16) : NES :=
  let s := { s with dmaPending := false, unmodelled := s.unmodelled || rendering s }
  let s := (readCycle s haltAddr).2
  let s := if s.cyc &&& 1 != 0 then (readCycle s haltAddr).2 else s
  go 256 0 s
where
  go : Nat → UInt16 → NES → NES
    | 0, _, s => s
    | n + 1, i, s =>
      let (b, s) := readCycle s ((s.dmaPage.toUInt16 <<< 8) ||| i)
      let s := ppuRegWrite (beginCycle s) 0x2004 b
      go n (i + 1) (endCycle { s with bus := b, padRead := 0 })

def rdS (s : NES) (a : UInt16) : UInt8 × NES :=
  readCycle (if s.dmaPending then oamDma s a else s) a

def wrS (s : NES) (a : UInt16) (b : UInt8) : NES :=
  let s := { beginCycle s with bus := b, padRead := 0 }
  let s :=
    if a < 0x2000 then s.setRam (a &&& 0x7FF).toNat b
    else if a < 0x4000 then ppuRegWrite s a b
    else if a == 0x4014 then { s with dmaPending := true, dmaPage := b }
    else if a == 0x4016 then
      let on := b &&& 1 != 0
      { s with strobe := on, polls := s.polls + (if s.strobe && !on then 1 else 0) }
    else if a == 0x4015 && b &&& 0x10 != 0 then { s with unmodelled := true }
    else s
  endCycle s

end NES

/-! ### CPU bus instance -/

instance : Bus NES where
  regs s := { pc := s.pc, a := s.a, x := s.x, y := s.y, s := s.s, p := s.p }
  setRegs s r := { s with pc := r.pc, a := r.a, x := r.x, y := r.y, s := r.s, p := r.p }
  read := NES.rdS
  write := NES.wrS
  idle := NES.tickS
  unsupported s := { s with unmodelled := true }
  nmiPending s := s.nmiPending
  clearNmiPending s := { s with nmiPending := false }
  nmiPolled s := s.nmiPolled
  setNmiPolled s b := { s with nmiPolled := b }

/-! ### Power, reset and frames -/

namespace NES

def resetVector (prg : ByteArray) : UInt16 :=
  (prg.get! 0x7FFC).toUInt16 ||| ((prg.get! 0x7FFD).toUInt16 <<< 8)

/-- The fixed power-on state used by this project, with RAM pattern 00 00 00 00 FF FF FF FF.
No theorem currently generalizes it to other cold-boot RAM or hardware startup phases. -/
def power (prg chr : ByteArray) (vertical : Bool := true) : NES :=
  let s := sched {
    prg, chr, vertical
    pc := resetVector prg, a := 0, x := 0, y := 0, s := 0xFD, p := 0x34
    ram := ⟨(Array.range 0x800).map fun i => if i &&& 4 != 0 then 0xFF else 0x00⟩
    ctrl := 0, mask := 0, oamaddr := 0, w := false, fx := 0, rbuf := 0
    vbl := false, spr0 := false, ovf := false, iolatch := 0, v := 0, t := 0
    ntram := ⟨Array.replicate 0x800 0⟩, pal := ⟨Array.replicate 32 0⟩, oam := ⟨Array.replicate 256 0⟩
    fpos := 22 * 341, flen := 262 * 341, overflowPos := NONE, hitPos := NONE, line := 0, sp0x := 0, sp0data := 0
    nextEv := 0, evIdx := 4, odd := 0, dead := 1, nmiPending := false, frameDone := false
    skipped := 0, suppressVbl := false, nmiLine := false, nmiPolled := false, dmaPending := false, dmaPage := 0
    pad0 := 0, pad1 := 0, sh0 := 0, sh1 := 0, strobe := false
    bus := 0, padRead := 0, padBit := 0, ioLow := 0, ioBit5 := 0, ioHigh := 0,
    polls := 0, unmodelled := false, cyc := 0 }
  (List.range 7).foldl (fun s _ => tickS s) s

/-- Reset CPU/register state without rewinding the running PPU clock. -/
def reset (s : NES) : NES :=
  let s := { s with
    s := s.s - 3, p := s.p ||| CPU.FI, ctrl := 0, mask := 0, w := false, vbl := false, dead := 1,
    nmiPending := false, nmiLine := false, nmiPolled := false, dmaPending := false,
    pc := resetVector s.prg }
  (List.range 7).foldl (fun s _ => tickS s) s

/-- Instruction budget per frame: far above the ~30,000 cycles a frame lasts. -/
def frameFuel : Nat := 100000

/-- Run one frame with the given controller bytes. -/
def frame (pad0 pad1 : UInt8) (s : NES) : NES :=
  go frameFuel { s with pad0, pad1, polls := 0, frameDone := false }
where
  go : Nat → NES → NES
    | 0, s => { s with unmodelled := true }
    | n + 1, s => if s.frameDone then s else go n (CPU.step.run s).2

/-- Run one frame per input byte (controller 2 idle). -/
def runFrames (inputs : List UInt8) (s : NES) : NES :=
  inputs.foldl (fun s b => frame b 0 s) s

end NES
end Smb
