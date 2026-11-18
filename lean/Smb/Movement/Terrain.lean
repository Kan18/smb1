import Smb.Movement.Model

/-!
# Mario's movement with tiles

`Smb.Movement.Model` with position and `PlayerBGCollision` for small Mario, on a fixed map without coin
pickups or block changes. The C searches in `analysis/movement` use the same abstraction. A proof relating
this terrain model to every relevant NES execution remains open.
-/
namespace Smb.Movement

/-- A stretch of the block buffer: 13 rows for each column from `base`. -/
structure Map where
  base : Nat
  data : ByteArray

def Map.tile (m : Map) (col row : Nat) : UInt8 :=
  if col < m.base then 0 else m.data.get! ((col - m.base) * 13 + row)

structure T where
  s : S
  pos : UInt32      -- `$6D` `$86` `$400`
  yh : UInt8        -- `$B5`
  coll : UInt8      -- `$490`
  t784 : UInt8
  evt : UInt8       -- sticky: 1 side pipe, 2 the pole, 3 down a pipe, 4 the axe
  deriving Hashable, Repr, Inhabited, DecidableEq

def T.pixel (t : T) : Nat := (t.pos >>> 8).toNat

/-- The tile at a sensor. `$E3B0` and `$E3CC` give the offsets for small Mario. -/
def tileAt (m : Map) (t : T) (xAdd yAdd : Nat) : UInt8 :=
  let px := t.pixel + xAdd
  let row := (((t.s.y.toNat + yAdd) &&& 0xF0) + 0x100 - 0x20) &&& 0xFF
  if row ≥ 0xD0 then 0 else m.tile (px / 16) (row / 16)

def tgroup (t : UInt8) : Nat := (t >>> 6).toNat
def solidT (t : UInt8) : Bool := t ≥ tbl5 0x10 0x61 0x88 0xC4 0 (tgroup t)
def climbT (t : UInt8) : Bool := t ≥ tbl5 0x24 0x6D 0x8A 0xC6 0 (tgroup t)
def coinT (t : UInt8) : Bool := t == 0xC2 || t == 0xC3

/-- `$DF4B`: a wall stops the speed and moves Mario off it. -/
def impede (t : T) (dir : UInt8) : T :=
  if dir == 1 then
    let t' := if t.s.v &&& 0x80 == 0 then { t with s := { t.s with v := 0 }, pos := (t.pos - 0x100) &&& 0xFFFFFF } else t
    { t' with coll := t'.coll &&& 0xFE }
  else
    let t' := if t.s.v &&& 0x80 != 0 || t.s.v == 0 then { t with s := { t.s with v := 0 }, pos := (t.pos + 0x100) &&& 0xFFFFFF } else t
    { t' with coll := t'.coll &&& 0xFD }

/-- The head sensor. -/
def headCheck (m : Map) (t : T) : T :=
  if t.s.y ≥ 0x10 then
    let c := tileAt m t 8 0x12
    if c != 0 && !coinT c && t.s.vy ≥ 0x80 && t.s.y &&& 15 ≥ 4 then
      if solidT c then { t with s := { t.s with vy := 1 } }
      else if t.t784 != 0 then { t with s := { t.s with vy := 1 } }
      else { t with t784 := 0x10, s := { t.s with vy := 0 } }
    else t
  else t

/-- A side sensor pair's result, tile or nothing. -/
def sideTile (m : Map) (t : T) (x : Nat) : Option UInt8 :=
  -- one tile can come from either sensor; both are at `Y` + `$18` for small Mario
  if t.s.y < 0x20 then
    if t.s.y < 8 then none else
    if t.s.y ≥ 0xD0 then some 0xFF else
    let c := tileAt m t x 0x18
    if c != 0 then some c else none
  else if t.s.y ≥ 0xE4 then some 0xFF
  else
    let c := tileAt m t x 0x18
    if c != 0 && c != 0x1C && c != 0x6B then some c
    else if c != 0 && climbT c then some c
    else if t.s.y ≥ 0xD0 then some 0xFF
    else if c != 0 then some c else none

/-- What a side tile does. `0xFF` above stands for the routine returning with nothing. -/
def sideHit (t : T) (c : UInt8) (dir : UInt8) : T :=
  if c == 0xFF || c == 0x5F || c == 0x60 then t
  else if climbT c then
    let nib := (t.pos >>> 8) &&& 15
    if 6 ≤ nib && nib < 10 then { t with evt := 2 } else t
  else if coinT c then t
  else
    let t' := if t.s.st == 0 && t.s.face == 1 && (c == 0x6C || c == 0x1F) then { t with evt := 1 } else t
    impede t' dir

/-- `PlayerBGCollision`, small Mario, without coins being taken or blocks changing. -/
def collide (m : Map) (down : Bool) (t0 : T) : T :=
  let t1 : T := if t0.s.st == 0 || t0.s.st == 3 then { t0 with s := { t0.s with st := 2 } } else t0
  if t1.yh != 1 then t1 else
  let t2 : T := { t1 with coll := 0xFF }
  if t2.s.y ≥ 0xCF then t2 else
  let t3 := headCheck m t2
  let l := tileAt m t3 3 0x20
  let r := tileAt m t3 0x0C 0x20
  let c : UInt8 := if coinT l || (l == 0 && coinT r) then 0 else if l != 0 then l else r
  let feet : Option T :=
    if c != 0 && !climbT c && t3.s.vy < 0x80 then
      if c == 0xC5 then some { t3 with evt := 4 }
      else if c != 0x5F && c != 0x60 then
        if t3.s.y &&& 15 < 5 then
          let e : UInt8 := if down && r == 0x11 && l == 0x10 then 3 else t3.evt
          some { t3 with evt := e, s := { t3.s with y := (t3.s.y &&& 0xF0), vy := 0, vf := 0, st := 0 } }
        else none
      else some t3
    else some t3
  match feet with
  | none => impede t3 t3.s.move
  | some t4 =>
    if t4.evt == 4 then t4 else
    match sideTile m t4 2 with
    | some c => sideHit t4 c 2
    | none =>
      match sideTile m t4 0x0D with
      | some c => sideHit t4 c 1
      | none => t4

/-- `ImposeFriction` with the walls' block on pressing into them. -/
def tFriction (lr jl maxr maxl : UInt8) (add : UInt16) (s : S) : S :=
  if s.st == 0 || lr != 0 then
    let lo := add.toUInt8
    let hi := (add >>> 8).toUInt8
    if jl != 0 && jl &&& 1 != 0 || jl == 0 && s.v != 0 && 0x80 ≤ s.v then
      let nv := rightV s.v s.f lo hi maxr
      { s with f := s.f + lo, v := nv, abs := absOf nv }
    else if jl != 0 || s.v != 0 then
      let nv := leftV s.v s.f lo hi maxl
      { s with f := s.f - lo, v := nv, abs := absOf nv }
    else { s with abs := 0 }
  else s

/-- `ImposeGravity`, with `$B5`. -/
def tFall (t : T) : T :=
  let s := t.s
  if s.st != 0 then
    let pos : UInt32 := (t.yh.toUInt32 <<< 16) ||| (s.y.toUInt32 <<< 8) ||| s.ysub.toUInt32
    let vel : UInt32 := ((if s.vy < 0x80 then s.vy.toUInt32 else s.vy.toUInt32 ||| 0xFFFFFF00) <<< 8) ||| s.vf.toUInt32
    let np := pos + vel
    let nv : UInt32 := ((s.vy.toUInt32 <<< 8) ||| s.vf.toUInt32) + s.g.toUInt32
    let cl : Bool := (nv >>> 8).toUInt8 - 4 &&& 0x80 == 0 && nv.toUInt8 ≥ 0x80
    let vy : UInt8 := if cl then 4 else (nv >>> 8).toUInt8
    let vf : UInt8 := if cl then 0 else nv.toUInt8
    { t with yh := (np >>> 16).toUInt8, s := { s with ysub := np.toUInt8, y := (np >>> 8).toUInt8, vy := vy, vf := vf } }
  else t

/-- One frame. -/
def tStep (m : Map) (i : In) (t0 : T) : T :=
  let rawlr : UInt8 := (if i.r then 1 else 0) ||| (if i.l then 2 else 0)
  let a : UInt8 := if i.a then 0x80 else 0
  let s0 := t0.s
  let lr : UInt8 := if i.down && s0.st == 0 then 0 else rawlr
  let s1 := jumpStart a { s0 with t783 := if s0.t783 != 0 then s0.t783 - 1 else 0 }
  let t784 : UInt8 := if t0.t784 != 0 then t0.t784 - 1 else 0
  let maxr := tbl3 0x28 0x18 0x10 (speedClass lr i.b s1)
  let maxl := tbl3 0xD8 0xE8 0xF0 (speedClass lr i.b s1)
  let flo : UInt16 := (tbl3 0xE4 0x98 0xD0 (frictionClass lr i.b s1)).toUInt16
  let add : UInt16 := if s1.face != s1.move then flo <<< 1 else flo
  let s2 := routine rawlr lr a i (timerSet lr i.b s1)
  let s3 := setMove (tFriction lr (lr &&& t0.coll) maxr maxl add s2)
  let p : UInt32 := (t0.pos + ((if s3.v < 0x80 then s3.v.toUInt32 else s3.v.toUInt32 ||| 0xFFFFFF00) * 16)) &&& 0xFFFFFF
  let t1 := tFall { t0 with s := s3, pos := p, t784 := t784 }
  collide m i.down { t1 with s := { t1.s with prevA := a } }

end Smb.Movement
