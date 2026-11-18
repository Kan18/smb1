import Smb.Game
import Smb.Tas

/-!
Replay and cartridge inspection for the Lean model.

* `smbcheck replay INPUT_BYTES OUT [STATES]` replays one controller-1 byte per frame.
* `smbcheck dump-tas OUT [STATES]` replays the target movie.
* `smbcheck rom ROMFILE` compares the file's PRG+CHR bytes with the embedded cartridge.

Both replay commands start from `initial` and write 2 KiB of RAM per frame to OUT.
STATES, if provided, receives complete model states.
-/
open Smb

-- Same field order and widths as dump_state in emu/replay.c.
def stateBytes (s : NES) : ByteArray := Id.run do
  let fields : List UInt64 := [
    s.pc.toUInt64, s.a.toUInt64, s.x.toUInt64, s.y.toUInt64,
    s.s.toUInt64, s.p.toUInt64, s.ctrl.toUInt64, s.mask.toUInt64,
    s.oamaddr.toUInt64, (if s.w then 1 else 0), s.fx.toUInt64, s.rbuf.toUInt64,
    (if s.vbl then 1 else 0), (if s.spr0 then 1 else 0), (if s.ovf then 1 else 0), s.iolatch.toUInt64,
    s.v.toUInt64, s.t.toUInt64, s.fpos.toUInt64, s.flen.toUInt64,
    s.hitPos.toUInt64, s.line.toUInt64, s.sp0x.toUInt64, s.sp0data.toUInt64,
    s.nextEv.toUInt64, s.evIdx.toUInt64, s.odd.toUInt64, s.dead.toUInt64,
    (if s.nmiPending then 1 else 0), (if s.frameDone then 1 else 0), s.pad0.toUInt64, s.pad1.toUInt64,
    s.sh0.toUInt64, s.sh1.toUInt64, (if s.strobe then 1 else 0), s.bus.toUInt64,
    s.polls.toUInt64, (if s.unmodelled then 1 else 0), s.cyc,
    (if s.vertical then 1 else 0), s.skipped.toUInt64, (if s.suppressVbl then 1 else 0),
    (if s.nmiLine then 1 else 0), (if s.nmiPolled then 1 else 0), (if s.dmaPending then 1 else 0),
    s.dmaPage.toUInt64, s.overflowPos.toUInt64, s.padRead.toUInt64, s.padBit.toUInt64,
    s.ioLow, s.ioBit5, s.ioHigh]
  let mut out := ByteArray.empty
  for v in fields do
    for j in [:8] do
      out := out.push ((v >>> (8 * j).toUInt64).toUInt8)
  return out ++ s.ram ++ s.ntram ++ s.pal ++ s.oam

def dumpInputs (inputs : List UInt8) (out : String) (stateOut : Option String) : IO UInt32 := do
  let h ← IO.FS.Handle.mk out .write
  let states ← stateOut.mapM fun path => IO.FS.Handle.mk path .write
  let mut s := initial
  let mut n := 0
  let mut victory : Option Nat := none
  for b in inputs do
    s := NES.frame b 0 s
    if s.unmodelled then
      IO.eprintln s!"unsupported execution at frame {n}, PC={s.pc}"
      return 1
    h.write s.ram
    if let some handle := states then handle.write (stateBytes s)
    if finalVictory s && victory.isNone then victory := some n
    n := n + 1
  IO.println s!"frames={n} finalVictory={finalVictory s} victoryFrame={victory} unmodelled={s.unmodelled}"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["dump-tas", out] => dumpInputs tasInputs out none
  | ["dump-tas", out, states] => dumpInputs tasInputs out (some states)
  | ["replay", inputs, out] =>
    let bytes ← IO.FS.readBinFile inputs
    dumpInputs bytes.toList out none
  | ["replay", inputs, out, states] =>
    let bytes ← IO.FS.readBinFile inputs
    dumpInputs bytes.toList out (some states)
  | ["rom", path] =>
    let raw ← IO.FS.readBinFile path
    let same := raw.extract 16 raw.size == rom
    IO.println s!"embedded ROM matches file: {same}"
    return if same then 0 else 1
  | _ => IO.eprintln "usage: smbcheck (dump-tas OUT [STATES] | replay INPUT_BYTES OUT [STATES] | rom ROMFILE)"; return 2
