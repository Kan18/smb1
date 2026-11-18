import Smb.Abs.Config

/-!
`smbabs ROM CONFIG`: run the box fixpoint and the checker from a text config (`Smb.Abs.Config`), and print what it needs.
-/
open Smb Smb.Abs Smb.Abs.Config

/-- Grow a chain of exact states: run the region on the states not yet run, and any state it exits with goes on the chain, until none is new.
It only finds the states. A full run of the region on all of them is what has to pass the checker.
Past the end of the level data, with every slot finished, the `chainTail` cells no longer matter, so those states leave them out. -/
def closeChain (c : C) (rom : UInt16 → UInt8) (g0 : Global) (track : List (Nat × Nat)) : IO UInt32 := do
  let base : Box := { pc := c.entry, s := c.s, a := c.a, x := c.x, y := c.y, p := c.p, cells := c.cells }
  let exact (b : Box) (i : UInt16) : Option UInt8 := match cellVS b.cells i with
    | some v => v.single?
    | none => none
  let rowOf (b : Box) : List (UInt16 × Option UInt8) := c.chainCells.map fun i => (i, exact b i)
  let inTail (r : List (UInt16 × Option UInt8)) : Bool :=
    let at_ (i : UInt16) := (r.lookup i).join
    c.chainEnds.any (fun (a, o) => at_ 0xE7 == some a && at_ 0x72C == some o) &&
      [0x730, 0x731, 0x732].all (fun (i : UInt16) => at_ i == some 0xFF)
  let canon (r : List (UInt16 × Option UInt8)) := if inTail r then r.map (fun (i, v) => if c.chainTail.contains i then (i, none) else (i, v)) else r
  let show' (r : List (UInt16 × Option UInt8)) := String.join (r.map fun (_, v) => match v with
    | some u => hex u.toNat 2
    | none => "..")
  let boxOf (r : List (UInt16 × Option UInt8)) : Box :=
    { base with cells := r.foldl (fun acc (i, v) => match v with
        | some u => Cells.set acc i (.set [u])
        | none => acc) base.cells }
  let mut g := g0
  let mut seen : Std.HashSet String := {}
  let mut frontier : List (List (UInt16 × Option UInt8)) := []
  for b in c.entries do
    let r := canon (rowOf b)
    if !seen.contains (show' r) then
      seen := seen.insert (show' r)
      frontier := r :: frontier
  let mut round := 0
  let t0 ← IO.monoMsNow
  while !frontier.isEmpty do
    round := round + 1
    let r := fixpoint (c.cfg rom g track) (frontier.map boxOf)
    if !r.finished then IO.println s!"round {round}: not finished"; return 1
    if !r.alarms.isEmpty then
      IO.println s!"round {round}: {r.alarms.toList.map (fun (pc, l) => (hex pc.toNat, l.take 2))}"
      return 1
    g := r.g
    let mut next : List (List (UInt16 × Option UInt8)) := []
    for b in r.table.getD (c.chainExit &&& 0x7FFF).toNat [] do
      let row := canon (rowOf b)
      -- a cell left wide outside the tail would lose what the chain is for
      if !inTail row && row.any (·.2.isNone) then
        IO.println s!"round {round}: exit not exact: {(row.filter (·.2.isNone)).map (fun (i, _) => hex i.toNat)}"
        return 1
      if !seen.contains (show' row) then
        seen := seen.insert (show' row)
        next := row :: next
    frontier := next
    if round % 500 == 0 then
      IO.eprintln s!"round {round}: chain {seen.size}, frontier {frontier.length}, {(← IO.monoMsNow) - t0} ms"
  if c.saveG != "" then
    let mut out := ""
    for i in [0:0x800] do
      match g[i]! with
      | .top => out := out ++ s!"global {hex i} top\n"
      | .set l => out := out ++ s!"global {hex i} {" ".intercalate (l.map (fun v => hex v.toNat 2))}\n"
    IO.FS.writeFile c.saveG out
  let hdr := "# " ++ " ".intercalate (c.chainCells.map (fun i => (hex i.toNat).dropWhile (· == '0') |>.toString))
  let rows := seen.toList.toArray.qsort (· < ·) |>.toList
  IO.FS.writeFile c.chainOut ("\n".intercalate (hdr :: rows) ++ "\n")
  IO.println s!"closed after {round} rounds: {seen.size} states, {(← IO.monoMsNow) - t0} ms"
  return 0

def main (args : List String) : IO UInt32 := do
  let [romPath, cfgPath] := args | do IO.eprintln "usage: smbabs ROM CONFIG"; return 2
  let bytes ← IO.FS.readBinFile romPath
  if bytes.size != 16 + 0xA000 || bytes[0]! != 0x4E || bytes[1]! != 0x45 || bytes[2]! != 0x53 || bytes[3]! != 0x1A || bytes[4]! != 2 || bytes[5]! != 1 || bytes[6]! &&& 0xFC != 0 || bytes[7]! &&& 0xF3 != 0 ||
      (!(bytes[7]! &&& 0x0C == 0 || bytes[7]! &&& 0x0C == 8)) ||
      (bytes[7]! &&& 0x0C == 8 && (bytes[8]! != 0 || bytes[9]! != 0)) then
    IO.eprintln "expected trainer-free NROM cartridge"; return 2
  let prg := bytes.extract 16 (16 + 0x8000)
  let rom : UInt16 → UInt8 := fun a => prg.get! (a &&& 0x7FFF).toNat
  let txt ← IO.FS.readFile cfgPath
  let c ← match parseChecked txt with
    | .ok c => pure c
    | .error e => do IO.eprintln e; return 2
  if c.chainOut != "" then return ← closeChain c rom c.globals c.track
  let mut g := c.globals
  let entries := c.entries
  let mut track := c.track
  let mut r : Result := default
  let mut cfg : Cfg := { rom, exit := fun _ => false, prot := fun _ => false, g, track := fun _ => false }
  let t0 ← IO.monoMsNow
  -- Cells whose global bound keeps growing become tracked per box; each is a hint the run found itself.
  let mut promoted : List UInt16 := []
  while true do
    cfg := c.cfg rom g track
    r := fixpoint cfg entries
    if r.promote.isEmpty then break
    for i in r.promote do
      if !promoted.contains i then promoted := i :: promoted
      track := (i.toNat, i.toNat) :: track
      g := g.set! i.toNat .top
    IO.println s!"promoted {r.promote.map (fun i => hex i.toNat)} after {r.steps} steps"
    (← IO.getStdout).flush
  let t1 ← IO.monoMsNow
  let mut pcs := 0
  for l in r.table do
    if !l.isEmpty then pcs := pcs + 1
  let mut nb := 0
  let mut ntop := 0
  for v in r.g do
    match v with
    | .top => ntop := ntop + 1
    | _ => nb := nb + 1
  IO.println s!"promoted cells {(promoted.map (fun i => hex i.toNat)).reverse}"
  IO.println s!"boxes {r.boxes}, steps {r.steps}, passes {r.passes}, finished {r.finished}, PCs {pcs}, alarm sites {r.alarms.size}, bounded cells {nb}, {t1 - t0} ms"
  let sorted := r.alarms.toList.toArray.qsort (fun a b => a.1 < b.1)
  for (pc, msgs) in sorted do
    IO.println s!"{hex pc.toNat} {msgs}"
  let dumpCells := c.dumpCells
  for a in c.dump do
    for b in r.table.getD (a &&& 0x7FFF).toNat [] do
      IO.println s!"dump {hex a.toNat} s={b.s} a={if b.a.elems.length < 20 then toString b.a.elems else s!"many({b.a.elems.length}, lacks {(List.range 256).filter (fun v => !b.a.mem (UInt8.ofNat v)) |>.take 12})"} x={if b.x.elems.length < 20 then toString b.x.elems else "many"} y={if b.y.elems.length < 20 then toString b.y.elems else "many"} p={b.p.elems.length} c0={(cellVS b.cells 2).map (·.elems.length)} cells={(b.cells.filter (fun e => e.1 < 0x10 || c.dumpCells.contains e.1 || e.1 == 0x300 || e.1 == 0x72C)).map (fun c => (hex c.1.toNat, if c.2.elems.length > 24 && !dumpCells.contains c.1 then [999] else c.2.elems.map UInt8.toNat))} ctx={b.ctx.map (fun u => hex u.toNat)}"
  for (pc, l) in r.writers.toList do
    IO.println s!"writes {hex pc.toNat}: {l.map (fun i => hex i.toNat)}"
  let mut linksOk := true
  for (pc, f) in c.nexts do
    let next ← match parseChecked (← IO.FS.readFile f) with
      | .ok c => pure c
      | .error e => do IO.eprintln s!"{f}: {e}"; return 2
    -- a cell this region may not write keeps what it held at this region's entry, so a box needn't show it again, but every entry here has to meet the bound there
    let keeps := fun (t : Box) => c.entries.all fun s => (t.cells.filter fun d => cfg.prot d.1).all fun d => cellCovered r.g s [] d
    let E := (next.entries.filter keeps).map fun e => { e with cells := e.cells.filter fun d => !cfg.prot d.1 }
    let boxes := r.table.getD (pc &&& 0x7FFF).toNat []
    let bad := boxes.filter fun b => !E.any (Box.le r.g b)
    linksOk := linksOk && bad.isEmpty
    IO.println s!"next {hex pc.toNat} {f}: {boxes.length} boxes, {bad.length} not contained"
    for b in bad.take 4 do
      let why := E.map fun e =>
        let cs := (e.cells.filter fun d => !cellCovered r.g b [] d).map fun d =>
          (hex d.1.toNat, (d.2.elems.length), match cellVS b.cells d.1 with
            | some v => if v.elems.length > 24 then [999] else v.elems.map UInt8.toNat
            | none => [998])
        s!"s={b.s}/{e.s} a={b.a.sub e.a} x={b.x.sub e.x} y={b.y.sub e.y} p={b.p.sub e.p} cells={cs}"
      IO.println s!"  {why}"
  if c.saveG != "" then
    let mut out := s!"# promoted {promoted.map (fun i => hex i.toNat)}\n"
    for i in [0:0x800] do
      match r.g[i]! with
      | .top => out := out ++ s!"global {hex i} top\n"
      | .set l => out := out ++ s!"global {hex i} {" ".intercalate (l.map (fun v => hex v.toNat 2))}\n"
    for i in promoted do
      out := out ++ s!"track {hex i.toNat}\n"
    IO.FS.writeFile c.saveG out
  for (st, l) in r.growLog do
    let sorted := l.toArray.qsort (fun a b => a.1 < b.1)
    IO.println s!"grew at step {st}: {sorted.map (fun (i, vs) => s!"{hex i.toNat}+{if vs.length > 8 then s!"{vs.length}vals" else toString vs}")}"
  let hs := r.hot.toList.toArray.qsort (fun a b => a.2 > b.2)
  IO.println s!"hot tuples: {(hs.toList.take 14).map (fun (a, n) => (hex a.toNat, n))}"
  let bc := (r.table.toList.zipIdx.map (fun (l, n) => (n + 0x8000, l.length))).toArray.qsort (fun a b => a.2 > b.2)
  IO.println s!"most boxes: {(bc.toList.take 14).map (fun (a, n) => (hex a, n))}"
  (← IO.getStdout).flush
  let mut accepted := false
  if r.finished && c.noCheck then
    IO.println "check skipped"
    return if linksOk && r.alarms.isEmpty then 3 else 1
  if r.finished then
    let tc ← IO.monoMsNow
    let ok := (if c.frame then checkF rom cfg.exit cfg.prot r.g r.table else if c.nes then checkN rom cfg.exit cfg.prot r.g r.table else check rom cfg.exit cfg.prot r.g r.table) && entries.all (entryIn r.g r.table)
    accepted := ok && linksOk
    let t2 ← IO.monoMsNow
    IO.println s!"check {ok} ({t2 - tc} ms)"
    if ok then
      -- `check` is true only given these: see `AssumedOk`, and the exits' `next` lines
      let boundOf := fun (i : Nat) => match r.g[i]! with
        | .top => "top"
        | .set l => s!"{(l.head?.map UInt8.toNat).getD 0}-{(l.getLast?.map UInt8.toNat).getD 0}"
      IO.println s!"assumed, not shown: 0300 in {boundOf 0x300}, 0340 in {boundOf 0x340} at every instruction"
      let openExits := c.exit.filter fun e =>
        !c.nexts.any (·.1 == e) && !(r.table.getD (e &&& 0x7FFF).toNat []).isEmpty
      IO.println s!"exits reached with no next region: {openExits.map (fun e => hex e.toNat)}"
    if !ok then
      let mut bad : List (String × String) := []
      for n in [0:0x8000] do
        for b in r.table.getD n [] do
          let fine := if c.frame then boxF rom cfg.exit cfg.prot r.g r.table b else cfg.exit b.pc || checkBox rom cfg.prot r.g r.table b || (c.nes && (ioBox rom r.g r.table b || loadBox rom r.g r.table b))
          let hdr := (b.pc &&& 0x7FFF).toNat == n && 0x8000 ≤ b.pc && (b.p.elems.all (fun p => p &&& 4 != 0))
          if !fine || !hdr then
            bad := (hex b.pc.toNat, s!"s={b.s} a={b.a.elems.length} x={b.x.elems.length} y={b.y.elems.length} p={b.p.elems} hdr={hdr}") :: bad
      IO.println s!"rejected boxes {bad.length}: {bad.reverse.take 10}"
      IO.println s!"entries in table: {entries.map (entryIn r.g r.table)}"
  return if accepted then 0 else 1
