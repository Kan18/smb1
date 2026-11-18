import Smb.Abs.CheckIO
import Std.Data.HashMap

/-!
# Computing a table of boxes

`fixpoint` runs the instructions forward from an entry box, joining states by a key, and returns the table with a list
of alarms: places where it could not keep the checker's conditions. Nothing here is trusted. `check` decides whether the
result is an invariant, and any alarm makes it fail. The key decides precision: PC, S, the return addresses on the
stack, exact X where it is a single value, and the flags where the next instruction reads them.
-/
namespace Smb.Abs
open Std

/-- A larger set counts as unknown. "`Y` below `$CF`", the game's check before block collisions, has to fit. -/
def setCap : Nat := 240

namespace VS
def insertSorted (v : UInt8) : List UInt8 → List UInt8
  | [] => [v]
  | x :: l => if v < x then v :: x :: l else if v == x then x :: l else x :: insertSorted v l
/-- Merge two sorted lists. Tail-recursive; the generator spends most of its time here. -/
def mergeSorted : List UInt8 → List UInt8 → List UInt8 → List UInt8
  | acc, [], b => acc.reverseAux b
  | acc, a, [] => acc.reverseAux a
  | acc, x :: l, y :: m =>
    if x < y then mergeSorted (x :: acc) l (y :: m)
    else if x == y then mergeSorted (x :: acc) l m
    else mergeSorted (y :: acc) (x :: l) m
def join : VS → VS → VS
  | .top, _ | _, .top => .top
  | .set a, .set b =>
    let r := mergeSorted [] a b
    if r.length > setCap then .top else .set r
def single? : VS → Option UInt8
  | .set [v] => some v
  | _ => none
def same : VS → VS → Bool
  | .top, .top => true
  | .set a, .set b => a == b
  | _, _ => false
def subSorted : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _, [] => false
  | x :: l, y :: m => if x == y then subSorted l m else if y < x then subSorted (x :: l) m else false
/-- Inclusion, for sorted sets. -/
def leq : VS → VS → Bool
  | _, .top => true
  | .top, _ => false
  | .set a, .set b => subSorted a b
end VS

structure Cfg where
  rom : UInt16 → UInt8
  exit : UInt16 → Bool
  prot : UInt16 → Bool
  g : Global
  /-- RAM cells tracked per box, besides the stack page. -/
  track : UInt16 → Bool
  splitA : UInt16 → Bool := fun _ => false
  /-- Where to keep A's values apart only by which side of these thresholds they're on: enough to carry a comparison's result, without a state per value. -/
  splitABands : UInt16 → List UInt8 := fun _ => []
  splitY : UInt16 → Bool := fun _ => false
  /-- Cells whose exact value separates states, for loop counters that run parallel to an index. -/
  splitCells : List UInt16 := []
  /-- `(i, lo, hi)`: from `lo` to `hi`, separate states by the exact value of cell `i`, for a loop's counter. -/
  splitCellsAt : List (UInt16 × UInt16 × UInt16) := []
  /-- `(i, lo, hi, gs)`: from `lo` to `hi`, separate states by the exact value of cell `i`, but only those where each cell of `gs` is at least its threshold: a split that only matters in the rare states. -/
  splitCellsIf : List (UInt16 × UInt16 × UInt16 × List (UInt16 × UInt8)) := []
  /-- `(i, lo, hi, ts)`: from `lo` to `hi`, separate states by which side of the thresholds cell `i` is on. -/
  splitCellBands : List (UInt16 × UInt16 × UInt16 × List UInt8) := []
  /-- `(base, i)`: where `splitViaAt` holds, separate states by the exact value of the cell at `base` plus the value of cell `i`. -/
  splitVia : List (UInt16 × UInt16) := []
  splitViaAt : UInt16 → Bool := fun _ => false
  maxSteps : Nat := 5000000
  /-- Report writes outside the global bounds instead of widening them. -/
  noGrow : Bool := false
  /-- Give up past this many boxes: memory is what runs out first. -/
  maxBoxes : Nat := 100000000
  promoteAfter : Nat := 1000000
  widenAfter : Nat := 600
  /-- Take the ALU fast path whenever A and the operand are both unknown, which loses only the flags' relation to them. -/
  fastTop : Bool := false
  /-- Cells whose global bound is a hypothesis about the run: writes to them don't grow it. -/
  assumed : UInt16 → Bool := fun _ => false
  /-- Cells whose bound stays as given: a write outside it is an alarm at the writer. -/
  pin : UInt16 → Bool := fun _ => false
  /-- Cells whose writers to report; nothing is rejected for it. -/
  watch : UInt16 → Bool := fun _ => false
  /-- A global bound that has grown in this many passes becomes unconstrained. -/
  boundWiden : Nat := 1000000
  /-- Code that needs no precision: widen after a few joins, which saves most of the revisits. -/
  widenFast : UInt16 → Bool := fun _ => false
  /-- Which box to step next: 0 the lowest PC, 1 the first discovered, 2 the last pushed. -/
  order : Nat := 0
  /-- The full NES: hardware accesses are steps, as in `checkN`. -/
  nes : Bool := false
  /-- Also the instructions between frames, as in `checkF`, and NMIs from the idle loop. -/
  frame : Bool := false

abbrev Key := List UInt16

/-- Which band of the thresholds a value is in. -/
def bandOf (ts : List UInt8) (v : UInt8) : Nat := ts.foldl (fun n t => if t ≤ v then n + 1 else n) 0

/-- The bits of P selected by `mask`, if every value in the set agrees on them. -/
def maskedKey (p : VS) (mask : UInt8) : UInt16 :=
  match p.elems with
  | [] => 999
  | v :: l => if l.all (fun u => u &&& mask == v &&& mask) then (v &&& mask).toUInt16 else 999

def flagKey (rom : UInt16 → UInt8) (pc : UInt16) (p : VS) : UInt16 :=
  match decode (rom pc) with
  | .branch mask _ => maskedKey p mask
  | .alu 3 _ | .alu 7 _ | .rmw 2 _ | .rmw 3 _ | .shiftA 2 | .shiftA 3 => maskedKey p 1
  | _ => 998

def keyOf (cfg : Cfg) (b : Box) : Key :=
  let xk : UInt16 := match b.x.single? with | some v => v.toUInt16 | none => 999
  let ak : UInt16 :=
    if cfg.splitA b.pc then (match b.a.single? with | some v => v.toUInt16 | none => 999)
    else match cfg.splitABands b.pc, b.a.elems with
      | [], _ | _, [] => 998
      | ts, v :: _ => (1000 + bandOf ts v).toUInt16
  let yk : UInt16 := if cfg.splitY b.pc then (match b.y.single? with | some v => v.toUInt16 | none => 999) else 998
  let ck := cfg.splitCells.map fun i =>
    match cellVS b.cells i with
    | some v => match v.single? with
      | some u => u.toUInt16
      | none => 999
    | none => 999
  let rk := (cfg.splitCellsAt.filter fun (_, lo, hi) => lo ≤ b.pc && b.pc ≤ hi).map fun (i, _, _) =>
    match cellVS b.cells i with
    | some v => match v.single? with
      | some u => u.toUInt16
      | none => 999
    | none => 999
  let gk := (cfg.splitCellsIf.filter fun (_, lo, hi, _) => lo ≤ b.pc && b.pc ≤ hi).map fun (i, _, _, gs) =>
    if gs.all (fun (g, t) => match cellVS b.cells g with
        | some gv => gv.elems.all (t ≤ ·)
        | none => false) then
      match cellVS b.cells i with
      | some v => match v.single? with
        | some u => u.toUInt16
        | none => 999
      | none => 999
    else 998
  let bk := (cfg.splitCellBands.filter fun (_, lo, hi, _) => lo ≤ b.pc && b.pc ≤ hi).map fun (i, _, _, ts) =>
    match cellVS b.cells i with
    | some v => match v.elems with
      | u :: _ => (bandOf ts u).toUInt16
      | [] => 998
    | none => 998
  let vk := (if cfg.splitViaAt b.pc then cfg.splitVia else []).map fun (base, i) =>
    match cellVS b.cells i with
    | some v => match v.single? with
      | some u => match cellVS b.cells (base + u.toUInt16) with
        | some w => match w.single? with
          | some e => e.toUInt16
          | none => 999
        | none => 999
      | none => 999
    | none => 999
  b.pc :: b.s.toUInt16 :: flagKey cfg.rom b.pc b.p :: xk :: ak :: yk :: (ck ++ rk ++ gk ++ bk ++ vk ++ b.ctx)

def Cells.join : Cells → Cells → Cells
  | [], _ | _, [] => []
  | (i, v) :: l, (j, w) :: m =>
    if i == j then
      match v.join w with
      | .top => Cells.join l m
      | u => (i, u) :: Cells.join l m
    else if i < j then Cells.join l ((j, w) :: m)
    else Cells.join ((i, v) :: l) m

def Cells.set : Cells → UInt16 → VS → Cells
  | [], i, v => [(i, v)]
  | (j, w) :: l, i, v =>
    if i == j then (i, v) :: l
    else if i < j then (i, v) :: (j, w) :: l
    else (j, w) :: Cells.set l i v

def Box.join (a b : Box) : Box :=
  { a with a := a.a.join b.a, x := a.x.join b.x, y := a.y.join b.y, p := a.p.join b.p,
           cells := Cells.join a.cells b.cells }

/-- Everything `b` allows, `a` allows too. A cell `a` doesn't list is unconstrained there. -/
def Cells.leq : Cells → Cells → Bool
  | _, [] => true
  | [], (_, v) :: m => (match v with | .top => Cells.leq [] m | _ => false)
  | (i, v) :: l, (j, w) :: m =>
    if i == j then v.leq w && Cells.leq l m
    else if i < j then Cells.leq l ((j, w) :: m)
    else (match w with | .top => Cells.leq ((i, v) :: l) m | _ => false)

/-- `b` adds nothing to `a`. Most joins find this, and this allocates nothing. -/
def Box.leq (b a : Box) : Bool :=
  b.a.leq a.a && b.x.leq a.x && b.y.leq a.y && b.p.leq a.p && Cells.leq b.cells a.cells

def Box.same (a b : Box) : Bool :=
  a.a.same b.a && a.x.same b.x && a.y.same b.y && a.p.same b.p &&
  a.cells.length == b.cells.length && (a.cells.zip b.cells).all fun (u, v) => u.1 == v.1 && u.2.same v.2

/-- Remove popped stack cells. -/
def pruneStack (s : UInt8) (c : Cells) : Cells :=
  c.filter fun e => !(0x100 ≤ e.1 && e.1 ≤ 0x100 + s.toUInt16)

def hex (n : Nat) (w : Nat := 4) : String :=
  let d := Nat.toDigits 16 n
  String.ofList (List.replicate (w - d.length) '0' ++ d)

structure Out where
  succ : HashMap Key Box := {}
  alarms : List (UInt16 × String) := []
  /-- Values written outside a global bound. -/
  grow : List (UInt16 × UInt8) := []
  tuples : Nat := 0
  /-- Global bounds this step read, so that growth redoes only the boxes it can affect. -/
  reads : List UInt16 := []
  /-- Watched cells this step wrote. -/
  watched : List UInt16 := []

/-- The global cell a read at `a` depends on, if the box does not track it. -/
def globalRead (b : Box) (a : UInt16) : Option UInt16 :=
  if a < 0x2000 then
    let i := a &&& 0x7FF
    if (cellVS b.cells i).isSome then none else some i
  else none

def addRead (l : List UInt16) (b : Box) (a : UInt16) : List UInt16 :=
  match globalRead b a with
  | some i => if l.contains i then l else i :: l
  | none => l

def addSucc (cfg : Cfg) (o : Out) (nb : Box) : Out :=
  let k := keyOf cfg nb
  match o.succ[k]? with
  | some old => { o with succ := o.succ.insert k (old.join nb) }
  | none => { o with succ := o.succ.insert k nb }

/-- An unknown register must not fan out into a state per value: if one key's states differ only by exact X,
merge those beyond a few values. The merged box has a set for X, so its key has no X in it. -/
def capFanout (cfg : Cfg) (o : Out) : Out :=
  if o.succ.size ≤ 8 then o else Id.run do
    let mut groups : HashMap Key (List Box) := {}
    for (_, b) in o.succ.toList do
      let k := keyOf cfg { b with x := .top }
      groups := groups.insert k (b :: groups.getD k [])
    let mut succ : HashMap Key Box := {}
    for (_, l) in groups.toList do
      if l.length > 8 then
        match l with
        | [] => pure ()
        | b :: r =>
          let m := r.foldl Box.join b
          succ := succ.insert (keyOf cfg m) m
      else
        for b in l do succ := succ.insert (keyOf cfg b) b
    return { o with succ }

/-- Call chain entries are (S at the JSR, return address) pairs: drop those the stack has popped,
which also handles `JumpEngine` discarding its return address with `pla`. -/
def ctxPop (s : UInt8) : List UInt16 → List UInt16
  | pos :: ret :: l => if pos.toNat ≤ s.toNat + 1 then ctxPop s l else pos :: ret :: l
  | l => l

/-- A byte set as four words, for fast accumulation. -/
structure Bits where
  w0 : UInt64 := 0
  w1 : UInt64 := 0
  w2 : UInt64 := 0
  w3 : UInt64 := 0
  deriving Inhabited

@[inline] def Bits.add (b : Bits) (v : UInt8) : Bits :=
  let m : UInt64 := 1 <<< (v &&& 63).toUInt64
  match v >>> 6 with
  | 0 => { b with w0 := b.w0 ||| m }
  | 1 => { b with w1 := b.w1 ||| m }
  | 2 => { b with w2 := b.w2 ||| m }
  | _ => { b with w3 := b.w3 ||| m }

def Bits.addVS (b : Bits) (t : VS) : Bits := t.elems.foldl Bits.add b

def Bits.has (b : Bits) (n : Nat) : Bool :=
  let w := match n / 64 with | 0 => b.w0 | 1 => b.w1 | 2 => b.w2 | _ => b.w3
  (w >>> (UInt64.ofNat (n % 64))) &&& 1 == 1

def Bits.toVS (b : Bits) : VS :=
  let l := (List.range 256).filter b.has
  if l.length > setCap then .top else .set (l.map UInt8.ofNat)

/-- The tuples that reach one successor. -/
structure Acc where
  pc : UInt16
  s : UInt8
  a : Bits := {}
  x : Bits := {}
  y : Bits := {}
  p : Bits := {}
  n : Nat := 0
  wr : List (UInt16 × Nat × Bits) := []
  /-- Values read from the data cell, if any: a cell not written holds what was read. -/
  rd : Bits := {}
  rdCell : Option UInt16 := none
  /-- When this successor was first seen, to iterate the successors in the order the key map would have. -/
  ord : Nat := 0

def Acc.addWrite (w : List (UInt16 × Nat × Bits)) (i : UInt16) (v : UInt8) : List (UInt16 × Nat × Bits) :=
  match w with
  | [] => [(i, 1, Bits.add {} v)]
  | (j, n, b) :: l => if i == j then (j, n + 1, b.add v) :: l else (j, n, b) :: Acc.addWrite l i v

/-- All successors of a box, by the same enumeration `checkBox` uses. -/
def stepBox (cfg : Cfg) (b : Box) : Out := Id.run do
  let rom := cfg.rom
  let g := cfg.g
  let pc := b.pc
  let k := decode (rom pc)
  let b1 := rom (pc + 1)
  let b2 := rom (pc + 2)
  let mut o : Out := {}
  if k == .unknown then
    return { o with alarms := [(pc, s!"unknown opcode s={b.s} ctx={b.ctx.map (fun u => hex u.toNat)}")] }
  if !(0x8000 ≤ pc && pc ≤ 0xFFF0) then
    return { o with alarms := [(pc, "pc out of ROM")] }
  if cfg.nes && ioKind k then
    let xs := regList (readsX k) b.x
    let ys := regList (readsY k) b.y
    let hw := xs.all fun x => ys.all fun y =>
      let a := operandAddr k b1 b2 ⟨pc, 0, x, y, b.s, 0⟩ 0 0
      0x2000 ≤ a && a < 0x8000
    if hw then
      for a in regList (readsA k) b.a do
        for x in xs do
          for y in ys do
            for p in b.p.elems do
              let r : Regs := ⟨pc, a, x, y, b.s, p⟩
              if !ioAddrOk k b1 b2 r && !(cfg.frame && pc == onEnter) then
                o := { o with alarms := (pc, s!"hardware store a={a} x={x} y={y}") :: o.alarms.take 7 }
      return addSucc cfg o { b with pc := pc + 3 }
  if cfg.nes && anyLoad k then
    let xs := regList (readsX k) b.x
    let ys := regList (readsY k) b.y
    -- a read of a hardware register, or through a pointer not known to stay in RAM and ROM
    let pa := ptrAddrs k b1 b2 ⟨pc, 0, 0, 0, b.s, 0⟩
    let hw := match k with
      | .load .a .indy =>
        ys.length * (readVS rom g b pa.1).elems.length * (readVS rom g b pa.2).elems.length > 4096 ||
        ys.any fun y => (readVS rom g b pa.1).elems.any fun lo => (readVS rom g b pa.2).elems.any fun hi =>
          !accessOk k b1 b2 ⟨pc, 0, 0, y, b.s, 0⟩ lo hi
      | _ => xs.length * ys.length ≥ 128 || xs.all fun x => ys.all fun y =>
        let a := operandAddr k b1 b2 ⟨pc, 0, x, y, b.s, 0⟩ 0 0
        0x2000 ≤ a && a < 0x8000
    if hw then
      let mut ps : Bits := {}
      for p in b.p.elems do
        for v in [0, 1, 0x80] do
          ps := ps.add (nz p v)
      let next := match k with
        | .load _ m => pc + m.size
        | _ => pc
      return addSucc cfg o { b with pc := next, p := ps.toVS,
                                    a := if writesA k then .top else b.a,
                                    x := if writesX k then .top else b.x,
                                    y := if writesY k then .top else b.y }
  -- A large product of unknowns gives an unknown result: take the checker's fast path.
  if aluFast k && accessOk k b1 b2 ⟨pc, 0, 0, 0, b.s, 0⟩ 0 0 then
    let reads := (regList (readsX k) b.x).foldl (fun n x =>
      (regList (readsY k) b.y).foldl (fun n y =>
        n + (regList (usesV k) (readVS rom g b (operandAddr k b1 b2 ⟨pc, 0, x, y, b.s, 0⟩ 0 0))).length) n) 0
    -- A compare leaves A alone, so only its flags are lost; other operations lose their result too.
    let limit := match k with
      | .alu 6 _ => 30000
      | _ => 200000
    let aTop := match b.a with | .top => true | _ => false
    if reads * b.a.elems.length * b.p.elems.length > limit || (cfg.fastTop && aTop && reads ≥ 64) then
      for x in regList (readsX k) b.x do
        for y in regList (readsY k) b.y do
          o := { o with reads := addRead o.reads b (operandAddr k b1 b2 ⟨pc, 0, x, y, b.s, 0⟩ 0 0) }
      let next := (eval k b1 b2 ⟨pc, 0, 0, 0, b.s, 0⟩ 0 0 0).regs.pc
      let ps := b.p.elems.foldl (fun acc p => (flagClosure p).foldl Bits.add acc) ({} : Bits)
      let nb : Box := { b with pc := next, a := (match k with | .alu 6 _ => b.a | _ => .top), p := ps.toVS }
      return addSucc cfg o nb
  -- A load that can reach memory with no bound: its result is unknown, so don't try each combination. The checker's `loadBox` accepts this.
  if cfg.fastTop && (match k with | .load .a .indy => true | _ => false) then
    let ys := regList (readsY k) b.y
    let pa := ptrAddrs k b1 b2 ⟨pc, 0, 0, 0, b.s, 0⟩
    let los := (readVS rom g b pa.1).elems
    let his := (readVS rom g b pa.2).elems
    if ys.length * los.length * his.length * b.p.elems.length ≥ 256 then
      let anyTop := ys.any fun y => los.any fun lo => his.any fun hi =>
        match readVS rom g b (operandAddr k b1 b2 ⟨pc, 0, 0, y, b.s, 0⟩ lo hi) with
        | .top => true
        | _ => false
      if anyTop then
        let next := (eval k b1 b2 ⟨pc, 0, 0, 0, b.s, 0⟩ 0 0 0).regs.pc
        let ps := b.p.elems.foldl (fun acc p => [nz p 0, nz p 1, nz p 0x80].foldl Bits.add acc) ({} : Bits)
        let o' := { o with reads := addRead (addRead o.reads b pa.1) b pa.2 }
        return addSucc cfg o' { b with pc := next, a := .top, p := ps.toVS }
  if storeFast k && b.a.elems.length * b.p.elems.length * (regList (readsX k) b.x).length * (regList (readsY k) b.y).length > 256 then
    let mut cells := b.cells
    let mut next := pc
    let mut bits : List (UInt16) := []
    for x in regList (readsX k) b.x do
      for y in regList (readsY k) b.y do
        let r : Regs := ⟨pc, 0, x, y, b.s, 0⟩
        let pa := ptrAddrs k b1 b2 r
        if usesPtr k then
          o := { o with reads := addRead (addRead o.reads b pa.1) b pa.2 }
        for lo in regList (usesPtr k) (readVS rom g b pa.1) do
          for hi in regList (usesPtr k) (readVS rom g b pa.2) do
            if !accessOk k b1 b2 r lo hi then
              o := { o with alarms := (pc, s!"access: x={x} y={y} lo={lo} hi={hi}") :: o.alarms }
              continue
            next := (eval k b1 b2 r lo hi 0).regs.pc
            let i := operandAddr k b1 b2 r lo hi &&& 0x7FF
            if cfg.prot i then
              o := { o with alarms := (pc, s!"write {hex i.toNat} (x={x} y={y} lo={lo} hi={hi}) xset={b.x.elems.length} c300={match cellVS b.cells 0x300 with | some v => v.elems.length | none => 999} ctx={b.ctx.map (fun u => hex u.toNat)}") :: o.alarms }
              continue
            if !bits.contains i then bits := i :: bits
            if cfg.watch i && !o.watched.contains i then o := { o with watched := i :: o.watched }
    for i in bits do
      for v in b.a.elems do
        if !(gAt g i).mem v && !cfg.assumed i then
          if cfg.pin i then o := { o with alarms := (pc, s!"pinned {hex i.toNat} := {v}") :: o.alarms }
          else o := { o with grow := (i, v) :: o.grow }
      if bits.length == 1 then
        -- one address: the store replaces whatever the cell held
        if (0x100 ≤ i && i ≤ 0x1FF) || cfg.track i || (cellVS cells i).isSome then
          cells := match b.a with
            | .top => cells.filter (·.1 != i)
            | _ => Cells.set cells i b.a
      else
        match cellVS cells i with
        | some t => cells := Cells.set cells i (t.join b.a)
        | none => pure ()
    if next != pc then
      o := addSucc cfg o { b with pc := next, cells }
    return { o with alarms := o.alarms.take 8 }
  let rdA := readsA k || writesA k
  let rdX := readsX k || writesX k
  let rdY := readsY k || writesY k
  let mut accs : HashMap (UInt64 × UInt64) Acc := {}
  let mut alarms : List (UInt16 × String) := []
  let mut nAlarm := 0
  let mut grow : List (UInt16 × UInt8) := []
  let mut tuples := 0
  let mut reads : List UInt16 := []
  let mut watched : List UInt16 := []
  for a in regList (readsA k) b.a do
    for x in regList (readsX k) b.x do
      for y in regList (readsY k) b.y do
        for p in b.p.elems do
          let r : Regs := ⟨pc, a, x, y, b.s, p⟩
          let pa := ptrAddrs k b1 b2 r
          let loS := readVS rom g b pa.1
          let hiS := readVS rom g b pa.2
          if usesPtr k then
            reads := addRead (addRead reads b pa.1) b pa.2
          if usesPtr k && (match loS, hiS with | .top, .top => true | _, _ => false) then
            if nAlarm < 8 then
              alarms := (pc, s!"indirect through unknown {hex pa.1.toNat} {hex pa.2.toNat} s={b.s} a={b.a.elems.length} ctx={b.ctx.map (fun u => hex u.toNat)} cells={b.cells.map (fun c => hex c.1.toNat)}") :: alarms
              nAlarm := nAlarm + 1
            continue
          for lo in regList (usesPtr k) loS do
            for hi in regList (usesPtr k) hiS do
              if !accessOk k b1 b2 r lo hi then
                if nAlarm < 8 then
                  alarms := (pc, s!"access: ea {hex (operandAddr k b1 b2 r lo hi).toNat} x={x} y={y} lo={lo} hi={hi} ctx={b.ctx.map (fun u => hex u.toNat)} a={b.a.elems} ysz={b.y.elems.length}") :: alarms
                  nAlarm := nAlarm + 1
                continue
              let vs := readVS rom g b (operandAddr k b1 b2 r lo hi)
              if usesV k then
                reads := addRead reads b (operandAddr k b1 b2 r lo hi)
              for v in regList (usesV k) vs do
                tuples := tuples + 1
                if tuples > 3000000 then
                  return { o with alarms := (pc, s!"too many combinations: a={b.a.elems.length} x={b.x.elems.length} y={b.y.elems.length} p={b.p.elems.length} lo={loS.elems.length} hi={hiS.elems.length} v={vs.elems.length}") :: alarms, tuples }
                let e := eval k b1 b2 r lo hi v
                if e.regs.p &&& 4 == 0 then
                  if nAlarm < 8 then
                    alarms := (pc, "I flag cleared") :: alarms
                    nAlarm := nAlarm + 1
                  continue
                if e.wr.any (fun w => cfg.prot (w.1 &&& 0x7FF)) then
                  if nAlarm < 8 then
                    alarms := (pc, s!"write {e.wr.map (fun w => (hex w.1.toNat, w.2))} (x={x} y={y})") :: alarms
                    nAlarm := nAlarm + 1
                  continue
                for w in e.wr do
                  if cfg.watch (w.1 &&& 0x7FF) && !watched.contains (w.1 &&& 0x7FF) then watched := (w.1 &&& 0x7FF) :: watched
                  if !(gAt g (w.1 &&& 0x7FF)).mem w.2 && !cfg.assumed (w.1 &&& 0x7FF) then
                    if cfg.pin (w.1 &&& 0x7FF) then
                      if nAlarm < 8 then
                        alarms := (pc, s!"pinned {hex (w.1 &&& 0x7FF).toNat} := {w.2} (x={x} y={y} a={a})") :: alarms
                        nAlarm := nAlarm + 1
                      continue
                    grow := (w.1 &&& 0x7FF, w.2) :: grow
                    if cfg.noGrow && nAlarm < 8 then
                      alarms := (pc, s!"bound {hex (w.1 &&& 0x7FF).toNat} := {w.2} (x={x} y={y} a={a})") :: alarms
                      nAlarm := nAlarm + 1
                -- local key: successor PC, S, flags where they are read, exact X, and written stack bytes
                let fk := flagKey rom e.regs.pc (.set [e.regs.p])
                let xk : Nat := if rdX then e.regs.x.toNat else 999
                let sw := e.wr.foldl (fun h w =>
                  if 0x100 ≤ w.1 &&& 0x7FF && w.1 &&& 0x7FF ≤ 0x1FF then h * 65599 + w.1.toNat * 256 + w.2.toNat else h) 0
                let yk : Nat := if cfg.splitY e.regs.pc then e.regs.y.toNat else 999
                let ak : Nat :=
                  if cfg.splitA e.regs.pc then e.regs.a.toNat
                  else match cfg.splitABands e.regs.pc with
                    | [] => 999
                    | ts => 1000 + bandOf ts e.regs.a
                let sw := match readCell k (operandAddr k b1 b2 r lo hi) with
                  | some i => sw * 2049 + i.toNat + 1
                  | none => sw * 2049
                -- The key `kq * 4294967311 + sw` as its quotient and remainder by 4294967311, so it stays in machine
                -- words: the same keys, without a big number per enumerated value.
                let kq : UInt64 := (((((e.regs.pc.toUInt64 * 256 + e.regs.s.toUInt64) * 1024 + fk.toUInt64) * 1024 +
                  xk.toUInt64) * 1024 + yk.toUInt64) * 1024 + ak.toUInt64)
                let key : UInt64 × UInt64 := (kq + (sw / 4294967311).toUInt64, (sw % 4294967311).toUInt64)
                let acc := accs.getD key { pc := e.regs.pc, s := e.regs.s, ord := accs.size }
                let rc := readCell k (operandAddr k b1 b2 r lo hi)
                let acc := { acc with
                  rd := if rc.isSome then acc.rd.add v else acc.rd,
                  rdCell := rc,
                  a := if rdA then acc.a.add e.regs.a else acc.a,
                  x := if rdX then acc.x.add e.regs.x else acc.x,
                  y := if rdY then acc.y.add e.regs.y else acc.y,
                  p := acc.p.add e.regs.p,
                  n := acc.n + 1,
                  wr := e.wr.foldl (fun w u => Acc.addWrite w (u.1 &&& 0x7FF) u.2) acc.wr }
                accs := accs.insert key acc
  o := { o with alarms, grow, tuples, reads, watched }
  -- In the order a map keyed by the whole number would iterate them, so the table is built as before.
  let mut byNat : HashMap Nat Acc := {}
  for (key, acc) in accs.toArray.qsort (fun u v => u.2.ord < v.2.ord) do
    byNat := byNat.insert (key.1.toNat * 4294967311 + key.2.toNat) acc
  for (_, acc) in byNat.toList do
    let mut cells := b.cells
    if let some i := acc.rdCell then
      if (cellVS cells i).isSome || cfg.track i then
        cells := match acc.rd.toVS with
          | .top => cells.filter (·.1 != i)
          | t => Cells.set cells i t
    for (i, n, bits) in acc.wr do
      let track := 0x100 ≤ i && i ≤ 0x1FF || cfg.track i
      let old := cellVS cells i
      if n ≥ acc.n then
        if track || old.isSome then
          cells := Cells.set cells i bits.toVS
      else
        match old with
        | some t => cells := Cells.set cells i (bits.addVS t).toVS
        | none => pure ()
    let nb : Box :=
      { pc := acc.pc, s := acc.s,
        a := if rdA then acc.a.toVS else b.a,
        x := if rdX then acc.x.toVS else b.x,
        y := if rdY then acc.y.toVS else b.y,
        p := acc.p.toVS,
        cells := if acc.s == b.s then cells else pruneStack acc.s cells,
        ctx := match k with
          | .jsr => b.s.toUInt16 :: (pc + 2) :: b.ctx
          | _ => if acc.s.toNat > b.s.toNat then ctxPop acc.s b.ctx else b.ctx }
    o := addSucc cfg o nb
  return capFanout cfg o

/-- The state an NMI from the idle loop enters the handler in. -/
def nmiSucc (cfg : Cfg) (b : Box) : Box := Id.run do
  let rom := cfg.rom
  let mut ps : Bits := {}
  let mut pushed : Bits := {}
  for p in b.p.elems do
    ps := ps.add (p ||| CPU.FI)
    pushed := pushed.add ((p &&& ~~~CPU.FB) ||| CPU.FU)
  let cells := Cells.set (Cells.set (Cells.set b.cells (stack b.s) (.set [(b.pc >>> 8).toUInt8])) (stack (b.s - 1)) (.set [b.pc.toUInt8])) (stack (b.s - 2)) pushed.toVS
  return { b with pc := base (rom 0xFFFA) (rom 0xFFFB), s := b.s - 3, p := ps.toVS, cells, ctx := [] }

structure Result where
  table : Table
  boxes : Nat
  steps : Nat
  alarms : HashMap UInt16 (List String)
  grow : HashMap UInt16 Bits
  finished : Bool
  passes : Nat
  g : Global
  hot : HashMap UInt16 Nat
  /-- Cells whose global bound kept growing: a run should track them per box instead. -/
  promote : List UInt16 := []
  /-- Per pass, the steps so far and the values added to each global bound. -/
  growLog : List (Nat × List (UInt16 × List UInt8)) := []
  /-- Per instruction, the watched cells it can write. -/
  writers : HashMap UInt16 (List UInt16) := {}
  deriving Inhabited

/-- The boxes waiting to be stepped, each once, lowest priority first. Entries are `priority * 2^24 + id`. -/
structure Sched where
  heap : Array Nat := #[]
  queued : Array Bool := #[]
  /-- With no priorities, a plain stack. -/
  lifo : Bool := false

partial def Sched.up (h : Array Nat) (i : Nat) : Array Nat :=
  if i == 0 then h else
    let p := (i - 1) / 2
    if h[i]! < h[p]! then Sched.up (h.swapIfInBounds i p) p else h

partial def Sched.down (h : Array Nat) (i : Nat) : Array Nat :=
  let l := 2 * i + 1
  let r := l + 1
  if l ≥ h.size then h else
    let c := if r < h.size && h[r]! < h[l]! then r else l
    if h[c]! < h[i]! then Sched.down (h.swapIfInBounds i c) c else h

def Sched.push (s : Sched) (id prio : Nat) : Sched :=
  if s.queued.getD id false then s else
    let queued := if id < s.queued.size then s.queued else s.queued ++ Array.replicate (id + 1 - s.queued.size) false
    let queued := queued.set! id true
    let e := prio * 16777216 + id
    if s.lifo then { s with heap := s.heap.push e, queued }
    else { s with heap := Sched.up (s.heap.push e) s.heap.size, queued }

/-- The next box's id, and the rest. -/
def Sched.pop (s : Sched) : Nat × Sched :=
  if s.lifo then
    let e := s.heap.back!
    let id := e % 16777216
    (id, { s with heap := s.heap.pop, queued := s.queued.set! id false })
  else
    let e := s.heap[0]!
    let id := e % 16777216
    let last := s.heap.back!
    let h := s.heap.pop
    let h := if h.isEmpty then h else Sched.down (h.set! 0 last) 0
    (id, { s with heap := h, queued := s.queued.set! id false })

partial def fixpoint (cfg0 : Cfg) (entry : List Box) : Result := Id.run do
  let mut cfg := cfg0
  let mut boxes : HashMap Key Box := {}
  let mut counts : HashMap Key Nat := {}
  let mut work : Sched := { lifo := cfg0.order == 2 }
  let mut ids : HashMap Key Nat := {}
  let mut byId : Array Key := #[]
  let prio := fun (o : Nat) (id : Nat) (pc : UInt16) => match o with
    | 0 => pc.toNat
    | 1 => id
    | _ => 0
  let mut alarms : HashMap UInt16 (List String) := {}
  let mut grow : HashMap UInt16 Bits := {}
  for b in entry do
    let k := keyOf cfg b
    match boxes[k]? with
    | some old => boxes := boxes.insert k (old.join b)
    | none =>
      boxes := boxes.insert k b
      ids := ids.insert k byId.size
      work := work.push byId.size (prio cfg.order byId.size b.pc)
      byId := byId.push k
  let mut steps := 0
  let mut passes := 0
  let mut hot : HashMap UInt16 Nat := {}
  let mut watch : HashMap UInt16 (List UInt16) := {}
  let mut growCount : HashMap UInt16 Nat := {}
  let mut readers : HashMap UInt16 (List Key) := {}
  let mut writers : List Key := []
  let mut promote : List UInt16 := []
  let mut growLog : List (Nat × List (UInt16 × List UInt8)) := []
  let mut finished := true
  repeat
    while !work.heap.isEmpty do
      if steps ≥ cfg.maxSteps || boxes.size > cfg.maxBoxes then
        finished := false
        break
      let (id, rest) := work.pop
      work := rest
      let k := byId[id]!
      let some b := boxes[k]? | continue
      if cfg.exit b.pc then continue
      steps := steps + 1
      let o := stepBox cfg b
      let o := if cfg.frame && b.pc == idlePC then addSucc cfg o (nmiSucc cfg b) else o
      if steps % 2000000 == 0 then
        work := dbgTrace s!"step {steps} boxes {boxes.size} work {work.heap.size} passes {passes} grown {grow.size} {(grow.toList.take 16).map (fun e => hex e.1.toNat)}" fun _ => work
      hot := hot.insert b.pc (hot.getD b.pc 0 + o.tuples)
      for i in o.watched do
        let l := watch.getD b.pc []
        if !l.contains i then watch := watch.insert b.pc (i :: l)
      for (pc, msg) in o.alarms do
        let l := alarms.getD pc []
        if l.isEmpty then
          alarms := dbgTrace s!"alarm at step {steps}: {hex pc.toNat} {msg.take 160}" fun _ => alarms.insert pc [msg]
        else if l.length < 3 && !l.contains msg then
          alarms := alarms.insert pc (msg :: l)
      for (i, v) in o.grow do
        grow := grow.insert i ((grow.getD i {}).add v)
      if !o.grow.isEmpty then writers := k :: writers
      for i in o.reads do
        readers := readers.insert i (k :: readers.getD i [])
      for (nk, nb) in o.succ.toList do
        match boxes[nk]? with
        | none =>
          boxes := boxes.insert nk nb
          ids := ids.insert nk byId.size
          work := work.push byId.size (prio cfg.order byId.size nb.pc)
          byId := byId.push nk
        | some old =>
          if nb.leq old then continue
          let j := old.join nb
          if !j.same old then
            let c := counts.getD nk 0 + 1
            counts := counts.insert nk c
            -- widen a key that keeps growing
            let j := if c > (if cfg.widenFast nb.pc then 6 else cfg.widenAfter) then
                { j with a := if j.a.same old.a then j.a else .top,
                         x := if j.x.same old.x then j.x else .top,
                         y := if j.y.same old.y then j.y else .top,
                         cells := j.cells.filter fun e =>
                           (0x100 ≤ e.1 && e.1 ≤ 0x1FF) || (old.cells.any fun d => d.1 == e.1 && d.2.same e.2) }
              else j
            boxes := boxes.insert nk j
            let nid := ids.getD nk 0
            work := work.push nid (prio cfg.order nid nb.pc)
    if !finished || grow.isEmpty || cfg.noGrow then break
    -- the code wrote outside some global bounds: widen them and redo every box
    let mut g := cfg.g
    let grownNow := grow.toList
    growLog := (steps, grownNow.map fun (i, b) => (i, b.toVS.elems)) :: growLog
    for (i, b) in grownNow do
      g := g.set! i.toNat ((b.addVS g[i.toNat]!).toVS)
      let c := growCount.getD i 0 + 1
      growCount := growCount.insert i c
      if c ≥ cfg.promoteAfter then promote := i :: promote
      if c ≥ cfg.boundWiden then g := g.set! i.toNat .top
    if !promote.isEmpty then break
    cfg := { cfg with g }
    grow := {}
    -- a pinned write isn't redone, so its alarm has to outlive the pass
    alarms := alarms.fold (init := {}) fun m pc l =>
      match l.filter (fun t => t.startsWith "pinned") with
      | [] => m
      | k => m.insert pc k
    passes := passes + 1
    let mut seen : HashMap Key Bool := {}
    for (i, _) in grownNow do
      for rk in readers.getD i [] do
        if !seen.contains rk then
          seen := seen.insert rk true
          let rid := ids.getD rk 0
          work := work.push rid (prio cfg.order rid (rk.headD 0))
      readers := readers.insert i []
    -- boxes that tried to write outside a bound were cut short there: redo them
    for rk in writers do
      if !seen.contains rk then
        seen := seen.insert rk true
        let rid := ids.getD rk 0
        work := work.push rid (prio cfg.order rid (rk.headD 0))
    writers := []
  let mut t : Table := Array.replicate 0x8000 []
  for (_, b) in boxes.toList do
    let n := (b.pc &&& 0x7FFF).toNat
    t := t.set! n (b :: t[n]!)
  return { table := t, boxes := boxes.size, steps, passes, g := cfg.g, hot, alarms, grow, finished, promote, writers := watch, growLog := growLog.reverse }

end Smb.Abs
