import Smb.Data.ProofRom
import Std.Data.HashSet

/-!
# An abstract machine for Mario's vertical state (for the floor-clip question)

Compiled with the model (so `native_decide` runs it natively); `Smb.Routine.FloorReach`
relates its arithmetic to the routine theorems and states the result.

State: Mario's position modulo 16 pixels with its sub-pixel (`pos`, 12 bits), his 8.8 velocity,
the active gravity and the falling gravity. Moves, each allowed whenever it might happen on
land (an over-approximation): jump start of any class 0–4 at any row offset, gravity per
frame with A held or not, stomp bounce (speed byte `$FC`/`$FD`), head bump (speed byte
`$01`/`$00`/`$FE`), landing on entering a row at offset < 5 followed by a jump, a jumpspring
bounce (speed `$F9`/`$F4`, gravity `$70`, at any offset), or walking off a ledge or lift (at any offset).
No vines, no water.
-/
namespace Smb.Vertical

structure Abs where
  pos : UInt16
  vel : UInt16
  vf : UInt8
  vfd : UInt8
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- `gravityVel 0 down 0 4 v` (see `Smb.Routine.gravityVel`). -/
def gravity (down : UInt8) (v : UInt16) : UInt16 :=
  let v1 := v + down.toUInt16
  bif (4 : UInt8).toBitVec.sle (v1 >>> 8).toUInt8.toBitVec && (0x80 ≤ v1.toUInt8 : Bool)
    then 0x0400 else v1

/-- Advance the 16-bit position in 1/256 px units. The successor masks it to a single tile row. -/
def move (pos v : UInt16) : UInt16 := pos + v

def jumpForce (c : Nat) : UInt8 := (smbPrgArray% 0xB424 5).getD c 0
def fallForce (c : Nat) : UInt8 := (smbPrgArray% 0xB42B 5).getD c 0
def jumpSpeed (c : Nat) : UInt8 := (smbPrgArray% 0xB432 5).getD c 0

/-- Jump starts for each class and row offset. The fractional bytes of
position and velocity are zero. -/
def jumps : List Abs :=
  (List.range 5).flatMap fun c => (List.range 16).map fun (off : Nat) =>
    ⟨(off.toUInt16 <<< 8 : UInt16), (jumpSpeed c).toUInt16 <<< 8, jumpForce c, fallForce c⟩

/-- A falling frame whose feet enter a new row (a 16-pixel boundary) at offset `≥ 5`. -/
def skipsWith (s : Abs) : Bool :=
  let p' := move s.pos s.vel
  s.vel < 0x8000 && (p' >>> 12) != (s.pos >>> 12) && (p' >>> 8) &&& 0x0F ≥ 5

/-- Entering a row at offset < 5 while falling: Mario may land there. -/
def mayLand (s : Abs) : Bool :=
  let p' := move s.pos s.vel
  s.vel < 0x8000 && (p' >>> 12) != (s.pos >>> 12) && (p' >>> 8) &&& 0x0F < 5

def succs (s : Abs) : List Abs :=
  let gs := if s.vel < 0x8000 then [s.vfd] else [s.vf, s.vfd]
  gs.flatMap fun g =>
    let p := move s.pos s.vel &&& 0x0FFF
    let v := gravity g s.vel
    -- Landing keeps the sub-pixel; walking off then starts at any offset (lifts), speed 0.
    let land := if mayLand s then
        (List.range 16).map (fun (off : Nat) =>
          (⟨(off.toUInt16 <<< 8 : UInt16) ||| (move s.pos s.vel &&& 0x00FF), 0, s.vfd, s.vfd⟩ : Abs))
          -- Jumpspring: speed $F9 or $F4, force 0, gravity $70. The handler moves Mario
          -- before the bounce, so this model allows any row offset.
          ++ (([0xF900, 0xF400] : List UInt16).flatMap fun (v : UInt16) => (List.range 16).map fun (off : Nat) =>
               (⟨(off.toUInt16 <<< 8 : UInt16) ||| (move s.pos s.vel &&& 0x00FF), v, 0x70, s.vfd⟩ : Abs))
          ++ jumps
      else []
    -- Stomp while falling ($FC/$FD); head bump while rising ($01 NYSpd, $00 BumpBlock,
    -- $FE BrickShatter); the force is kept in both.
    let bounce := if v < 0x8000 then [⟨p, 0xFC00 ||| (v &&& 0xFF), g, s.vfd⟩, ⟨p, 0xFD00 ||| (v &&& 0xFF), g, s.vfd⟩]
      else [⟨p, 0x0100 ||| (v &&& 0xFF), g, s.vfd⟩, ⟨p, v &&& 0xFF, g, s.vfd⟩, ⟨p, 0xFE00 ||| (v &&& 0xFF), g, s.vfd⟩]
    land ++ ⟨p, v, g, s.vfd⟩ :: bounce

/-- Breadth-first closure of `jumps` under `succs` (fuel: the number of states to process). -/
def reachable (fuel : Nat := 4000000) : Std.HashSet Abs := Id.run do
  let mut seen : Std.HashSet Abs := {}
  let mut todo : Array Abs := #[]
  for s in jumps do
    unless seen.contains s do seen := seen.insert s; todo := todo.push s
  let mut i := 0
  while i < todo.size && i < fuel do
    for t in succs todo[i]! do
      unless seen.contains t do seen := seen.insert t; todo := todo.push t
    i := i + 1
  return seen

/-- The certificate: `R` contains the jumps, is closed under `succs`, and has no skip. -/
def certifies (R : Std.HashSet Abs) : Bool :=
  jumps.all R.contains && R.toList.all fun s => !skipsWith s && (succs s).all R.contains

end Smb.Vertical
