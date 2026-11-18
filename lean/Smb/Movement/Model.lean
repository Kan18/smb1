import Std.Data.HashMap

/-!
# Mario's movement on open ground

A small state machine for the player routines' effect on one frame, with no walls, enemies or blocks, away from the screen's edge. Position isn't part of the state: nothing here reads it, so a frame's only effect on it is to add `adv`.

It's written from the routine summaries (`jumpRam`, `xphysRam`, `animRam`, `frictionRam`, `mphRam`, `gravityRam`), and the searches in `analysis/movement` use the same rules. `Smb.Goal.StartRun` states the connection to the game as a hypothesis.
-/
namespace Smb.Movement

structure S where
  v : UInt8        -- `$57`
  f : UInt8        -- `$705`
  abs : UInt8      -- `$700`
  face : UInt8     -- `$33`
  move : UInt8     -- `$45`
  st : UInt8       -- `$1D`
  t783 : UInt8
  r703 : UInt8
  y : UInt8        -- `$CE`
  ysub : UInt8     -- `$416`
  vy : UInt8       -- `$9F`
  vf : UInt8       -- `$433`
  g : UInt8        -- `$709`
  gfall : UInt8    -- `$70A`
  y0 : UInt8       -- `$708`
  rise : UInt8     -- `$706`
  prevA : UInt8    -- `$0D`'s A bit
  deriving Hashable, Repr, Inhabited, DecidableEq

/-- What a frame can act on: the buttons, and whether the `$783` timer is running. `other` is Up, Select or Start, which only `$6FC`'s skid check sees. The timer's an input because the routine only asks if it's zero, so the model needn't follow it. -/
structure In where
  r : Bool
  l : Bool
  b : Bool
  a : Bool
  other : Bool
  down : Bool
  timer : Bool
  deriving Inhabited, DecidableEq

def jumpClass (a : UInt8) : Nat := if a < 9 then 0 else if a < 0x10 then 1 else if a < 0x19 then 2 else if a < 0x1C then 3 else 4
def tbl5 (a b c d e : UInt8) : Nat → UInt8
  | 0 => a | 1 => b | 2 => c | 3 => d | _ => e
def tbl3 (a b c : UInt8) : Nat → UInt8
  | 0 => a | 1 => b | _ => c

/-- A jump starts on A's press, from the ground. -/
def jumpStart (a : UInt8) (s : S) : S :=
  if a != 0 && s.prevA == 0 && s.st == 0 then
    let c := jumpClass s.abs
    { s with ysub := 0, vf := 0, g := tbl5 0x20 0x20 0x1E 0x28 0x28 c, gfall := tbl5 0x70 0x70 0x60 0x90 0x90 c,
             vy := tbl5 0xFC 0xFC 0xFC 0xFB 0xFB c, st := 1, y0 := s.y, rise := 1 }
  else s

def running (lr : UInt8) (b : Bool) (s : S) : Bool :=
  if s.st == 0 then lr == s.move && (b || s.t783 != 0) else 0x19 ≤ s.abs

def speedClass (lr : UInt8) (b : Bool) (s : S) : Nat := if running lr b s then 0 else 1
def frictionClass (lr : UInt8) (b : Bool) (s : S) : Nat :=
  if running lr b s then 0 else if s.r703 != 0 || 0x21 ≤ s.abs then 2 else 1

/-- The `$783` timer restarts while running on the ground. -/
def timerSet (lr : UInt8) (b : Bool) (s : S) : S :=
  if s.st == 0 && lr == s.move && b then { s with t783 := 0x0A } else s

/-- On the ground: the skid check, then facing. -/
def skid (mask lr : UInt8) (s : S) : S :=
  let s1 : S :=
    if 0x1C ≤ s.abs then { s with r703 := s.abs }
    else if mask != 0 && (mask &&& 3) == s.move then { s with r703 := 0 }
    else if mask != 0 && s.abs < 0x0B then { s with move := s.face, v := 0, f := 0 }
    else s
  if lr != 0 then { s1 with face := lr } else s1

/-- What the state's routine does before friction. -/
def routine (rawlr lr a : UInt8) (i : In) (s : S) : S :=
  if s.st == 0 then
    skid (rawlr ||| (if i.b then 0x40 else 0) ||| (if i.other || i.down then 0x20 else 0)) lr s
  else if s.st == 1 then
    if (s.vy < 0x80 || !(a != 0 && s.prevA != 0)) && (s.vy < 0x80 || (s.y0 - s.y) ≥ s.rise) then { s with g := s.gfall } else s
  else { s with g := s.gfall }

/-- The speed after friction, the right way. -/
def rightV (v f lo hi maxr : UInt8) : UInt8 :=
  let raw := v + hi + (if f.toUInt16 + lo.toUInt16 > 255 then 1 else 0)
  if (raw - maxr) &&& 0x80 == 0 then maxr else raw

/-- The speed after friction, the left way. -/
def leftV (v f lo hi maxl : UInt8) : UInt8 :=
  let raw := v - hi - (if f < lo then 1 else 0)
  if (raw - maxl) &&& 0x80 == 0 then raw else maxl

def absOf (v : UInt8) : UInt8 := if v &&& 0x80 != 0 then 0 - v else v

/-- `ImposeFriction`: on the ground always, in the air only with a direction held. -/
def friction (lr maxr maxl : UInt8) (add : UInt16) (s : S) : S :=
  if s.st == 0 || lr != 0 then
    let lo := add.toUInt8
    let hi := (add >>> 8).toUInt8
    if lr != 0 && lr &&& 1 != 0 || lr == 0 && s.v != 0 && 0x80 ≤ s.v then
      let nv := rightV s.v s.f lo hi maxr
      { s with f := s.f + lo, v := nv, abs := absOf nv }
    else if lr != 0 || s.v != 0 then
      let nv := leftV s.v s.f lo hi maxl
      { s with f := s.f - lo, v := nv, abs := absOf nv }
    else { s with abs := 0 }
  else s

/-- `$B141`: the moving direction follows the speed's sign. -/
def setMove (s : S) : S := if s.v != 0 then { s with move := if s.v < 0x80 then 1 else 2 } else s

/-- `ImposeGravity`. -/
def fallS (s : S) : S :=
  if s.st != 0 then
    let pos : UInt32 := (s.y.toUInt32 <<< 8) ||| s.ysub.toUInt32
    let vel : UInt32 := ((if s.vy < 0x80 then s.vy.toUInt32 else s.vy.toUInt32 ||| 0xFFFFFF00) <<< 8) ||| s.vf.toUInt32
    let np := pos + vel
    let nv : UInt32 := ((s.vy.toUInt32 <<< 8) ||| s.vf.toUInt32) + s.g.toUInt32
    let cl : Bool := (nv >>> 8).toUInt8 - 4 &&& 0x80 == 0 && nv.toUInt8 ≥ 0x80
    let vy : UInt8 := if cl then 4 else (nv >>> 8).toUInt8
    let vf : UInt8 := if cl then 0 else nv.toUInt8
    { s with ysub := np.toUInt8, y := (np >>> 8).toUInt8, vy := vy, vf := vf }
  else s

/-- Landing on a floor at `Y` `ground`. -/
def land (ground : UInt8) (s : S) : S :=
  if s.st != 0 && s.vy < 0x80 && s.y ≥ ground && s.y &&& 15 < 5 && s.y < ground + 16 then
    { s with y := s.y &&& 0xF0, vy := 0, vf := 0, st := 0 }
  else s

/-- `PlayerMovementSubs` up to gravity, from the state after the frame's timers. -/
def moved (i : In) (s0 : S) : S :=
  let rawlr : UInt8 := (if i.r then 1 else 0) ||| (if i.l then 2 else 0)
  let a : UInt8 := if i.a then 0x80 else 0
  let lr : UInt8 := if i.down && s0.st == 0 then 0 else rawlr
  let s1 := jumpStart a s0
  let maxr := tbl3 0x28 0x18 0x10 (speedClass lr i.b s1)
  let maxl := tbl3 0xD8 0xE8 0xF0 (speedClass lr i.b s1)
  let flo : UInt16 := (tbl3 0xE4 0x98 0xD0 (frictionClass lr i.b s1)).toUInt16
  let add : UInt16 := if s1.face != s1.move then flo <<< 1 else flo
  let s2 := routine rawlr lr a i (timerSet lr i.b s1)
  friction lr maxr maxl add s2

def preFall (i : In) (s0 : S) : S := setMove (moved i s0)

/-- One frame, every cell. -/
def rawStep (ground : UInt8) (i : In) (s0 : S) : S :=
  { land ground (fallS (preFall i { s0 with t783 := if i.timer then 1 else 0 })) with prevA := if i.a then 0x80 else 0 }

/-- What a stretch of terrain allows: a floor to start on, and from `walkAt` on, a lower one to fall to, by walking off if `walks`. More progress only allows more, so keeping the most progress per state stays sound. -/
structure Mode where
  top : UInt8
  low : UInt8
  walkAt : Int
  walks : Bool

/-- Cells nothing can read any more, and `$783`, which comes with each frame's input. On the ground a jump overwrites these before reading them, except that walking off a floor reads `ysub` and `gfall`. Falling, the routine overwrites `g` and nothing reads the rest. A held A only matters on the way up: on the way down it's free to let go, so a landing needn't count as holding it. -/
def norm (m : Mode) (s : S) : S :=
  if s.st == 0 then
    if m.walks then { s with t783 := 0, vy := 0, vf := 0, g := 0, y0 := 0, rise := 0, prevA := 0 }
    else { s with t783 := 0, ysub := 0, vy := 0, vf := 0, g := 0, gfall := 0, y0 := 0, rise := 0, prevA := 0 }
  else if s.vy < 0x80 then { s with t783 := 0, g := 0, y0 := 0, rise := 0, prevA := 0 }
  else { s with t783 := 0 }

/-- The speed's byte as a signed number. -/
def signed (v : UInt8) : Int := if v < 0x80 then (v.toNat : Int) else (v.toNat : Int) - 256

/-- What a frame adds to the position, in 256ths of a pixel, from the state after it. -/
def adv (s : S) : Int := signed s.v * 16

/-- The speed's in range. -/
def speedOk (v : UInt8) : Bool := v ≤ 0x28 || 0xD8 ≤ v

/-- `other` and `down` together act as `down`, so `inputs` leaves that case out. -/
def inputs : List In :=
  [false, true].flatMap fun r => [false, true].flatMap fun l => [false, true].flatMap fun b => [false, true].flatMap fun a =>
    [false, true].flatMap fun t => [(false, false), (true, false), (false, true)].map fun (o, d) => ⟨r, l, b, a, o, d, t⟩

/-- A frame leaves the player alone, as a paused frame does, or runs it with an input, over a floor at `Y` `ground`, perhaps walking off one. -/
inductive Frame where
  | still
  | go (ground : UInt8) (leave : Bool) (i : In)
  deriving DecidableEq

/-- In the air only these buttons do anything. -/
def airInputs : List In :=
  [false, true].flatMap fun r => [false, true].flatMap fun l => [false, true].flatMap fun a => [false, true].map fun t => ⟨r, l, false, a, false, false, t⟩

/-- The floors to try. -/
def Mode.floors (m : Mode) (p : Int) : List UInt8 :=
  if m.walkAt ≤ p && m.low != m.top then [m.top, m.low] else [m.top]

/-- The frames to try from `s` at progress `p`. -/
def frames (m : Mode) (s : S) (p : Int) : List Frame :=
  .still :: if s.st == 0 then (m.floors p).flatMap fun g => (if m.walks && m.walkAt ≤ p then [false, true] else [false]).flatMap fun l => inputs.map (.go g l)
    else (m.floors p).flatMap fun g => airInputs.map (.go g false)

/-- The frames `m` allows from `s` at progress `p`. -/
def Frame.allowed (m : Mode) (s : S) (p : Int) : Frame → Prop
  | .still => True
  | .go g l _ => (g = m.top ∨ (g = m.low ∧ m.walkAt ≤ p)) ∧ (l = true → m.walks = true ∧ s.st = 0 ∧ m.walkAt ≤ p)

/-- One frame, on the cells that matter. -/
def step (m : Mode) (g : UInt8) (l : Bool) (i : In) (s : S) : S :=
  let t := rawStep g i s
  norm m (if l && t.st == 0 then { t with st := 2 } else t)

def nextS (m : Mode) : Frame → S → S
  | .still, s => s
  | .go g l i, s => step m g l i s

/-- What a frame adds to the position. -/
def delta (m : Mode) : Frame → S → Int
  | .still, _ => 0
  | .go g l i, s => adv (step m g l i s)

/-- Open ground at the start of 1-1. -/
def openGround : Mode := ⟨176, 176, 0, false⟩

/-- Mario at the first frame of control in 1-1. -/
def start : S :=
  { v := 0, f := 0, abs := 0, face := 1, move := 0, st := 0, t783 := 0, r703 := 0, y := 176, ysub := 0, vy := 0, vf := 0,
    g := 0, gfall := 0, y0 := 0, rise := 0, prevA := 0 }

def starts : Array (S × Int) := #[(start, 0)]

/-! ## Checking a search

A layer lists states with the most progress found for each. `layerOk` doesn't trust how the layers were made: every state and input has to land on an entry with at least that progress, or be unable to beat `goal` even at the speed limit. -/

abbrev Layer := Array (S × Int)

/-- Next layer from this one, keeping the most progress per state and dropping what can't beat the goal. -/
def nextLayer (m : Mode) (goal : Int) (left : Nat) (l : Layer) : Layer := Id.run do
  let mut h : Std.HashMap S Int := {}
  for (s, p) in l do
    for o in frames m s p do
      let t := nextS m o s
      let q := p + delta m o s
      if q + 640 * (left : Int) > goal then
        match h[t]? with
        | some r => if q > r then h := h.insert t q
        | none => h := h.insert t q
  return h.toArray

/-- The search: layer `n` is what's left after `n` frames. -/
def layers (m : Mode) (st : Layer) (goal : Int) (T : Nat) : List Layer := Id.run do
  let mut cur : Layer := st
  let mut out : List Layer := [cur]
  for n in [0:T] do
    cur := nextLayer m goal (T - n - 1) cur
    out := cur :: out
  return out.reverse

/-- A step from `(s, p)` is accounted for in `next`. -/
def stepOk (md : Mode) (goal : Int) (left : Nat) (m : Std.HashMap S Int) (s : S) (p : Int) (o : Frame) : Bool :=
  let t := nextS md o s
  let q := p + delta md o s
  decide (q + 640 * (left : Int) ≤ goal) ||
    (match m[t]? with
     | some r => decide (q ≤ r)
     | none => false)

def layerOk (md : Mode) (goal : Int) (left : Nat) (l next : Layer) : Bool :=
  let m : Std.HashMap S Int := next.foldl (fun m e => m.insert e.1 e.2) {}
  l.all fun e => speedOk e.1.v && (frames md e.1 e.2).all (stepOk md goal left m e.1 e.2)

def chainOk (md : Mode) (goal : Int) : Nat → List Layer → Bool
  | _, [] => false
  | _, [_] => true
  | left + 1, l :: n :: r => layerOk md goal left l n && chainOk md goal left (n :: r)
  | 0, _ :: _ :: _ => false

/-- The whole check, for `T` frames from `st` and target `goal`: the last layer is empty. -/
def verified (m : Mode) (st : Layer) (goal : Int) (T : Nat) : Bool :=
  let ls := layers m st goal T
  match ls with
  | [] => false
  | l :: _ => decide (l = st) && chainOk m goal T ls && (ls.getLast?.map (·.isEmpty)).getD false

end Smb.Movement
