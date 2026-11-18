import Smb.Abs.Fix

/-!
# Regions as text

A region is a text config: `entry PC S`, `exit PC`, `prot ADDR [ADDR2]`, `global ADDR v v v | global ADDR lo-hi`, `track ADDR [ADDR2]`,
`cell ADDR v v ...` (entry cell), `a`/`x`/`y`/`p v v ..`, `case ADDR=v,v ADDR=v` (one entry box per case), and the precision hints
`splita PC PC2`, `splity PC PC2`, `splitc CELLS`, `splitcr CELL PC PC2`, `splitv BASE CELL`, `widen PC PC2`. Numbers are hex. `smbabs` runs one and prints what it
needs, and a module can hold one and have `Config.accepted` compute its table and check it.
-/
namespace Smb.Abs.Config
open Smb Smb.Abs

def hx (s : String) : Nat := s.foldl (fun n c =>
  n * 16 + (if c.isDigit then c.toNat - 48 else (c.toLower.toNat - 97 + 10))) 0

def parseVals (ws : List String) : VS :=
  match ws with
  | ["top"] => .top
  | _ =>
    let l := ws.flatMap fun w =>
      match w.splitOn "-" with
      | [a, b] => (List.range (hx b - hx a + 1)).map fun i => UInt8.ofNat (hx a + i)
      | _ => [UInt8.ofNat (hx w)]
    .set (l.foldl (fun acc v => VS.insertSorted v acc) [])

structure C where
  entry : UInt16 := 0
  s : UInt8 := 0xFF
  exit : List UInt16 := []
  prot : List (Nat × Nat) := []
  track : List (Nat × Nat) := []
  splitA : List (Nat × Nat) := []
  splitAB : List (Nat × Nat × List UInt8) := []
  splitY : List (Nat × Nat) := []
  g : List (UInt16 × VS) := []
  cells : Cells := []
  a : VS := .top
  x : VS := .top
  y : VS := .top
  p : VS := .set [0x24, 0x25, 0x26, 0x27, 0xA4, 0xA5, 0xA6, 0xA7, 0x64, 0x65, 0x66, 0x67, 0xE4, 0xE5, 0xE6, 0xE7]
  max : Nat := 5000000
  maxBoxes : Nat := 100000000
  noGrow : Bool := false
  noCheck : Bool := false
  chainExit : UInt16 := 0
  chainOut : String := ""
  chainCells : List UInt16 := []
  chainTail : List UInt16 := []
  chainEnds : List (UInt8 × UInt8) := []
  assumed : List (Nat × Nat) := []
  pin : List (Nat × Nat) := []
  nes : Bool := false
  frame : Bool := false
  widen : List (Nat × Nat) := []
  watch : List (Nat × Nat) := []
  fastTop : Bool := false
  boundWiden : Nat := 1000000
  order : Nat := 0
  cases : List (List (UInt16 × VS)) := []
  saveG : String := ""
  splitCells : List UInt16 := []
  splitCellsAt : List (UInt16 × UInt16 × UInt16) := []
  splitCellsIf : List (UInt16 × UInt16 × UInt16 × List (UInt16 × UInt8)) := []
  splitCellBands : List (UInt16 × UInt16 × UInt16 × List UInt8) := []
  splitVia : List (UInt16 × UInt16) := []
  splitViaAt : List (Nat × Nat) := []
  dumpCells : List UInt16 := []
  nexts : List (UInt16 × String) := []
  dump : List UInt16 := []
  promoteAfter : Nat := 6

def inR (l : List (Nat × Nat)) (a : UInt16) : Bool := l.any fun (u, v) => u ≤ a.toNat && a.toNat ≤ v

private def parseUnchecked (txt : String) : C := Id.run do
  let mut c : C := {}
  for line in txt.splitOn "\n" do
    let ws := ((line.splitOn "#").head!.splitOn " ").filter (· != "")
    let rng (l : List String) : Nat × Nat :=
      match l with
      | [a] => (hx a, hx a)
      | a :: b :: _ => (hx a, hx b)
      | [] => (0, 0)
    match ws with
    | "entry" :: pc :: s :: _ => c := { c with entry := UInt16.ofNat (hx pc), s := UInt8.ofNat (hx s) }
    | "exit" :: pc :: _ => c := { c with exit := UInt16.ofNat (hx pc) :: c.exit }
    | "prot" :: r => c := { c with prot := rng r :: c.prot }
    | "track" :: r => c := { c with track := rng r :: c.track }
    | "splita" :: r => c := { c with splitA := rng r :: c.splitA }
    | "splitab" :: a :: b :: r => c := { c with splitAB := (hx a, hx b, r.map fun w => UInt8.ofNat (hx w)) :: c.splitAB }
    | "splity" :: r => c := { c with splitY := rng r :: c.splitY }
    | "global" :: a :: r => c := { c with g := (UInt16.ofNat (hx a), parseVals r) :: c.g }
    | "cell" :: a :: r => c := { c with cells := Cells.set c.cells (UInt16.ofNat (hx a)) (parseVals r) }
    | "a" :: r => c := { c with a := parseVals r }
    | "x" :: r => c := { c with x := parseVals r }
    | "y" :: r => c := { c with y := parseVals r }
    | "p" :: r => c := { c with p := parseVals r }
    | "max" :: n :: _ => c := { c with max := hx n }
    | "maxboxes" :: n :: _ => c := { c with maxBoxes := hx n }
    | "nogrow" :: _ => c := { c with noGrow := true }
    | "nocheck" :: _ => c := { c with noCheck := true }
    | "chain" :: pc :: out :: r => c := { c with chainExit := UInt16.ofNat (hx pc), chainOut := out, chainCells := r.map (fun w => UInt16.ofNat (hx w)) }
    | "chaintail" :: r => c := { c with chainTail := r.map (fun w => UInt16.ofNat (hx w)) }
    | "chainend" :: a :: b :: _ => c := { c with chainEnds := ((hx a).toUInt8, (hx b).toUInt8) :: c.chainEnds }
    | "pin" :: r => c := { c with pin := rng r :: c.pin }
    | "assume" :: a :: r => c := { c with g := (UInt16.ofNat (hx a), parseVals r) :: c.g, assumed := (hx a, hx a) :: c.assumed }
    | "nes" :: _ => c := { c with nes := true }
    | "fast" :: _ => c := { c with fastTop := true }
    | "watch" :: r => c := { c with watch := rng r :: c.watch }
    | "gwiden" :: n :: _ => c := { c with boundWiden := hx n }
    | "order" :: n :: _ => c := { c with order := hx n }
    | "widen" :: r => c := { c with widen := rng r :: c.widen }
    | "frame" :: _ => c := { c with nes := true, frame := true }
    | "case" :: r =>
      -- `case ADDR=v,v ADDR=v`: one entry box, with these cells on top of the common ones
      let cs := r.map fun w =>
        match w.splitOn "=" with
        | [a, vs] => (UInt16.ofNat (hx a), parseVals (vs.splitOn ","))
        | _ => (0, VS.top)
      c := { c with cases := cs :: c.cases }
    | "saveg" :: f :: _ => c := { c with saveG := f }
    | "splitvr" :: r => c := { c with splitViaAt := rng r :: c.splitViaAt }
    | "splitv" :: b :: i :: _ => c := { c with splitVia := (UInt16.ofNat (hx b), UInt16.ofNat (hx i)) :: c.splitVia }
    | "splitc" :: r => c := { c with splitCells := r.map (fun w => UInt16.ofNat (hx w)) ++ c.splitCells }
    | "splitcg" :: a :: lo :: hi :: r =>
      let rec pairs : List String → List (UInt16 × UInt8)
        | g :: t :: l => (UInt16.ofNat (hx g), UInt8.ofNat (hx t)) :: pairs l
        | _ => []
      c := { c with splitCellsIf := (UInt16.ofNat (hx a), UInt16.ofNat (hx lo), UInt16.ofNat (hx hi), pairs r) :: c.splitCellsIf }
    | "splitcb" :: a :: lo :: hi :: r => c := { c with splitCellBands := (UInt16.ofNat (hx a), UInt16.ofNat (hx lo), UInt16.ofNat (hx hi), r.map fun w => UInt8.ofNat (hx w)) :: c.splitCellBands }
    | "splitcr" :: a :: lo :: hi :: _ => c := { c with splitCellsAt := (UInt16.ofNat (hx a), UInt16.ofNat (hx lo), UInt16.ofNat (hx hi)) :: c.splitCellsAt }
    | "next" :: pc :: f :: _ => c := { c with nexts := (UInt16.ofNat (hx pc), f) :: c.nexts }
    | "dumpc" :: r => c := { c with dumpCells := r.map (fun w => UInt16.ofNat (hx w)) ++ c.dumpCells }
    | "dump" :: r => c := { c with dump := r.map (fun w => UInt16.ofNat (hx w)) ++ c.dump }
    | "promote" :: n :: _ => c := { c with promoteAfter := hx n }
    | _ => pure ()
  return c

private def number (s : String) (limit : Nat) : Except String Nat := do
  if s.isEmpty || !s.toList.all (fun c => c.isDigit || ('a' ≤ c.toLower && c.toLower ≤ 'f')) then
    throw s!"invalid hexadecimal number: {s}"
  let n := hx s
  if n > limit then throw s!"number out of range: {s}"
  return n

private def values (xs : List String) : Except String Unit := do
  if xs == ["top"] then return
  if xs.isEmpty then throw "empty value set"
  for x in xs do
    match x.splitOn "-" with
    | [a] => discard (number a 255)
    | [a,b] =>
      let lo ← number a 255
      let hi ← number b 255
      if hi < lo then throw s!"reversed range: {x}"
    | _ => throw s!"invalid value: {x}"

private def rangeArgs (xs : List String) (limit : Nat) : Except String Unit := do
  match xs with
  | [a] => discard (number a limit)
  | [a,b] =>
    let lo ← number a limit
    let hi ← number b limit
    if hi < lo then throw "reversed address range"
  | _ => throw "expected one address or two range endpoints"

/-- Validate the complete config before interpreting it. Invalid text is never silently ignored. -/
def parseChecked (txt : String) : Except String C := do
  let txt := (txt.replace "\t" " ").replace "\r" ""
  let mut seenEntry := false
  let mut globals : List Nat := []
  for (line, ix) in (txt.splitOn "\n").zipIdx do
    let ws := (((line.splitOn "#").head!).splitOn " ").filter (· != "")
    let result : Except String Unit := do
      match ws with
      | [] => pure ()
      | ["entry", pc, sp] =>
        discard (number pc 65535); discard (number sp 255)
      | ["exit", pc] => discard (number pc 65535)
      | "global" :: a :: vs | "cell" :: a :: vs | "assume" :: a :: vs =>
        discard (number a 2047); values vs
      | "a" :: vs | "x" :: vs | "y" :: vs | "p" :: vs => values vs
      | "case" :: cs =>
        if cs.isEmpty then throw "empty case"
        for c in cs do
          match c.splitOn "=" with
          | [a,v] => discard (number a 2047); values (v.splitOn ",")
          | _ => throw "expected ADDR=VALUES"
      | "prot" :: r | "track" :: r | "watch" :: r | "pin" :: r => rangeArgs r 2047
      | "chain" :: pc :: _ :: r =>
        discard (number pc 65535)
        for w in r do discard (number w 2047)
      | "chaintail" :: r => for w in r do discard (number w 2047)
      | ["chainend", x, y] => discard (number x 255); discard (number y 255)
      | "splita" :: r | "splity" :: r | "splitvr" :: r | "widen" :: r => rangeArgs r 65535
      | "splitab" :: a :: b :: r => discard (number a 65535); discard (number b 65535); for w in r do discard (number w 255)
      | "splitc" :: r | "dumpc" :: r =>
        if r.isEmpty then throw "empty cell list"
        for a in r do discard (number a 2047)
      | "dump" :: r =>
        if r.isEmpty then throw "empty PC list"
        for a in r do discard (number a 65535)
      | ["splitv", b, i] => discard (number b 2047); discard (number i 2047)
      | "splitcg" :: a :: lo :: hi :: r | "splitcb" :: a :: lo :: hi :: r =>
        discard (number a 2047); discard (number lo 65535); discard (number hi 65535)
        for w in r do discard (number w 2047)
      | ["splitcr", a, lo, hi] => discard (number a 2047); discard (number lo 65535); discard (number hi 65535)
      | ["max", n] | ["maxboxes", n] | ["promote", n] | ["gwiden", n] | ["order", n] => discard (number n 0xFFFFFFFF)
      | ["saveg", _] => pure ()
      | ["next", pc, _] => discard (number pc 65535)
      | ["nogrow"] | ["nocheck"] | ["nes"] | ["frame"] | ["fast"] => pure ()
      | _ => throw "unknown directive or wrong argument count"
    match result with
    | .error e => throw s!"line {ix+1}: {e}"
    | .ok _ => pure ()
    match ws with
    | "entry" :: _ =>
      if seenEntry then throw s!"line {ix+1}: duplicate entry"
      seenEntry := true
    | "global" :: a :: _ | "assume" :: a :: _ =>
      let n := hx a
      if globals.contains n then throw s!"line {ix+1}: duplicate global bound"
      globals := n :: globals
    | _ => pure ()
  if !seenEntry then throw "missing entry"
  return parseUnchecked txt

/-- Invalid embedded configs become an invalid entry (PC zero), so certificate checks fail. -/
def parse (txt : String) : C := (parseChecked txt).toOption.getD {}

def C.globals (c : C) : Global := Id.run do
  let mut g : Global := Array.replicate 0x800 VS.top
  for (i, v) in c.g do
    g := g.set! i.toNat v
  return g

def C.entries (c : C) : List Box :=
  let entry0 : Box := { pc := c.entry, s := c.s, a := c.a, x := c.x, y := c.y, p := c.p, cells := c.cells }
  if c.cases.isEmpty then [entry0]
  else c.cases.map fun cs => { entry0 with cells := cs.foldl (fun acc e => Cells.set acc e.1 e.2) entry0.cells }

def C.exitFn (c : C) (a : UInt16) : Bool := c.exit.contains a
def C.protFn (c : C) (a : UInt16) : Bool := inR c.prot a

def C.cfg (c : C) (rom : UInt16 → UInt8) (g : Global) (track : List (Nat × Nat)) : Cfg :=
  { rom, exit := c.exitFn, prot := c.protFn, g,
    track := inR track, splitA := inR c.splitA,
    splitABands := fun a => (c.splitAB.find? fun (lo, hi, _) => lo ≤ a.toNat && a.toNat ≤ hi).elim [] (·.2.2), splitY := inR c.splitY, maxSteps := c.max, maxBoxes := c.maxBoxes, noGrow := c.noGrow, nes := c.nes,
    frame := c.frame, widenFast := inR c.widen, watch := inR c.watch, assumed := inR c.assumed, pin := inR c.pin, fastTop := c.fastTop, boundWiden := c.boundWiden, order := c.order,
    promoteAfter := c.promoteAfter, splitCells := c.splitCells, splitCellsAt := c.splitCellsAt, splitCellsIf := c.splitCellsIf, splitCellBands := c.splitCellBands, splitVia := c.splitVia, splitViaAt := inR c.splitViaAt }

/-- The table a config computes, with its bounds fixed. -/
def C.table (c : C) (prg : ByteArray) : Table := (fixpoint (c.cfg (romOf prg) c.globals c.track) c.entries).table

/-- One computation of the table, accepted by `checkF` as containing every entry box. -/
def C.acceptedF (c : C) (prg : ByteArray) : Bool :=
  let T := c.table prg
  checkF (romOf prg) c.exitFn c.protFn c.globals T && c.entries.all (entryIn c.globals T)

/-- A region of a frame, against shared bounds `G`: its table, accepted by `checkF` as containing its entry boxes, and with its boxes at each listed exit
contained in the next region's entry boxes. -/
def C.tableWith (c : C) (G : Global) (prg : ByteArray) : Table :=
  (fixpoint (c.cfg (romOf prg) G c.track) c.entries).table

def C.linked (c : C) (G : Global) (prg : ByteArray) (nexts : List (UInt16 × List Box)) : Bool :=
  let T := c.tableWith G prg
  checkF (romOf prg) c.exitFn c.protFn G T && c.entries.all (entryIn G T) &&
  nexts.all fun (pc, E) => (T.at pc).all fun b => E.any (Box.le G b)

/-- As `linked`, with no box at the addresses `empties`. -/
def C.linkedE (c : C) (G : Global) (prg : ByteArray) (nexts : List (UInt16 × List Box)) (empties : List UInt16) : Bool :=
  let T := c.tableWith G prg
  checkF (romOf prg) c.exitFn c.protFn G T && c.entries.all (entryIn G T) &&
  (nexts.all fun (pc, E) => (T.at pc).all fun b => E.any (Box.le G b)) &&
  empties.all fun pc => (T.at pc).isEmpty

end Smb.Abs.Config
