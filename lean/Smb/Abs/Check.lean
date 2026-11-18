import Smb.Abs.Sem

/-!
# A checker for state descriptions

A `Box` describes machine states: the PC and S exactly, value sets for A, X, Y and P, and value sets for some RAM
cells. A table of boxes, one list per ROM address, is an invariant if every state a box allows steps to a state
another box allows. `checkBox` tests this by running `eval` on every combination of the values an instruction
actually reads, so it has no transfer functions to get wrong. It also rejects any write to a protected address and any
write outside `global`, a flow-insensitive list of cell bounds. `Smb.Routine.AbsCheck` proves it sound.
-/
namespace Smb.Abs

inductive VS where
  | top
  | set (l : List UInt8)
  deriving Inhabited, BEq, Repr

def allBytes : List UInt8 := (List.range 256).map UInt8.ofNat

namespace VS
def mem : VS → UInt8 → Bool
  | .top, _ => true
  | .set l, v => l.contains v
def elems : VS → List UInt8
  | .top => allBytes
  | .set l => l
/-- Inclusion; `false` is allowed to be conservative. -/
def sub : VS → VS → Bool
  | _, .top => true
  | .top, .set _ => false
  | .set l, t => l.all t.mem
/-- Strictly increasing, as the generator and the parser keep value sets. -/
def ascending : List UInt8 → Bool
  | x :: y :: l => x < y && ascending (y :: l)
  | _ => true

/-- Inclusion of strictly increasing lists, in one merge pass. -/
def subAsc : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: l, y :: m => if x == y then subAsc l m else if y < x then subAsc (x :: l) m else false

theorem ascending_tail {x : UInt8} {l : List UInt8} (h : ascending (x :: l) = true) : ascending l = true := by
  cases l with
  | nil => rfl
  | cons y l => simp only [ascending, Bool.and_eq_true] at h; exact h.2

theorem lt_of_ascending : ∀ {x : UInt8} {l : List UInt8}, ascending (x :: l) = true → ∀ v ∈ l, x < v
  | _, [], _, v, hv => absurd hv List.not_mem_nil
  | x, y :: l, h, v, hv => by
    simp only [ascending, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hv with rfl | hv
    · exact h.1
    · have := lt_of_ascending h.2 v hv
      exact UInt8.lt_iff_toNat_lt.mpr (Nat.lt_trans (UInt8.lt_iff_toNat_lt.mp h.1) (UInt8.lt_iff_toNat_lt.mp this))

theorem subAsc_iff : ∀ (l m : List UInt8), ascending l = true → ascending m = true →
    (subAsc l m = true ↔ ∀ v ∈ l, v ∈ m)
  | [], _, _, _ => by simp [subAsc]
  | x :: l, [], _, _ => by
    simp only [subAsc, Bool.false_eq_true, false_iff]
    intro h
    exact List.not_mem_nil (h x List.mem_cons_self)
  | x :: l, y :: m, hl, hm => by
    have hlt := lt_of_ascending hl
    have hmt := lt_of_ascending hm
    have hl' := ascending_tail hl
    have hm' := ascending_tail hm
    have ne_of_lt : ∀ {a b : UInt8}, a < b → a ≠ b := fun h e => by
      subst e; exact absurd (UInt8.lt_iff_toNat_lt.mp h) (Nat.lt_irrefl _)
    by_cases hxy : x = y
    · subst hxy
      simp only [subAsc, beq_self_eq_true, ↓reduceIte]
      rw [subAsc_iff l m hl' hm']
      constructor
      · intro h v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h v hv)
      · intro h v hv
        rcases List.mem_cons.mp (h v (List.mem_cons_of_mem _ hv)) with e | hv'
        · exact absurd e.symm (ne_of_lt (hlt v hv))
        · exact hv'
    · have hb : (x == y) = false := by simpa using hxy
      by_cases hyx : y < x
      · simp only [subAsc, hb, hyx, ↓reduceIte, Bool.false_eq_true]
        rw [subAsc_iff (x :: l) m hl hm']
        constructor
        · intro h v hv; exact List.mem_cons_of_mem _ (h v hv)
        · intro h v hv
          rcases List.mem_cons.mp (h v hv) with e | hv'
          · subst e
            rcases List.mem_cons.mp hv with e | hv
            · exact absurd e (ne_of_lt hyx)
            · have := hlt _ hv
              exact absurd (UInt8.lt_iff_toNat_lt.mp (show v < x from hyx))
                (Nat.lt_asymm (UInt8.lt_iff_toNat_lt.mp this))
          · exact hv'
      · simp only [subAsc, hb, hyx, ↓reduceIte, Bool.false_eq_true]
        constructor
        · intro h; exact absurd h (by decide)
        · intro h
          have hx := h x List.mem_cons_self
          rcases List.mem_cons.mp hx with e | hx
          · exact absurd e hxy
          · have h1 := hmt x hx
            have h2 : ¬ (y.toNat < x.toNat) := fun h' => hyx (UInt8.lt_iff_toNat_lt.mpr h')
            have h3 : x.toNat ≠ y.toNat := fun e => hxy (UInt8.toNat_inj.mp e)
            have := UInt8.lt_iff_toNat_lt.mp h1
            omega

theorem subAsc_eq {l m : List UInt8} (hl : ascending l = true) (hm : ascending m = true) :
    subAsc l m = l.all (fun v => m.contains v) := by
  apply Bool.eq_iff_iff.mpr
  rw [subAsc_iff l m hl hm, List.all_eq_true]
  simp

/-- Identical finite sets need only a linear equality test, rather than quadratic membership tests; increasing ones
a merge. -/
def subFast : VS → VS → Bool
  | _, .top => true
  | .top, .set _ => false
  | .set l, .set m => withPtrEq l m (fun _ => (l == m) ||
      (if ascending l && ascending m then subAsc l m else l.all (fun v => m.contains v)))
      (fun h => by subst h; simp)

@[csimp] theorem sub_eq_fast : VS.sub = subFast := by
  funext t u
  cases t with
  | top => cases u <;> rfl
  | set l =>
    cases u with
    | top => rfl
    | set m =>
      have hs : VS.sub (.set l) (.set m) = l.all (fun v => m.contains v) := rfl
      rw [hs, subFast, withPtrEq]
      by_cases h : l = m
      · subst m
        simp [List.all_eq_true]
      · have hm : (l == m) = false := by
          cases hb : l == m with
          | false => rfl
          | true => exact False.elim (h (beq_iff_eq.mp hb))
        rw [hm, Bool.false_or]
        cases ha : (ascending l && ascending m) with
        | true =>
          simp only [Bool.and_eq_true] at ha
          simp only [↓reduceIte]
          exact (subAsc_eq ha.1 ha.2).symm
        | false => simp only [Bool.false_eq_true, ↓reduceIte]
end VS

abbrev Cells := List (UInt16 × VS)

/-- Flow-insensitive bounds on RAM: one value set per address; anything past the end is unconstrained. -/
abbrev Global := Array VS

def gAt (g : Global) (i : UInt16) : VS := g.getD i.toNat .top

structure Box where
  pc : UInt16
  s : UInt8
  a : VS
  x : VS
  y : VS
  p : VS
  cells : Cells
  /-- For the table's producer only: the return addresses of the current call chain. It constrains nothing. -/
  ctx : List UInt16 := []
  deriving Inhabited, Repr

/-- The instruction classes' dependence on registers and on read memory values. -/
def Mode.usesX : Mode → Bool | .zpx | .absx | .indx => true | _ => false
def Mode.usesY : Mode → Bool | .zpy | .absy | .indy => true | _ => false
def Mode.indirect : Mode → Bool | .indx | .indy => true | _ => false

def readsA : Kind → Bool
  | .alu _ _ | .store .a _ | .cmp .a _ | .bit _ | .shiftA _ | .xfer .a _ | .pha => true
  | _ => false
def readsX : Kind → Bool
  | .alu _ m | .load _ m | .bit m | .rmw _ m => m.usesX
  | .store r m | .cmp r m => r == .x || m.usesX
  | .incdec r _ => r == .x
  | .xfer r _ => r == .x
  | .txs => true
  | _ => false
def readsY : Kind → Bool
  | .alu _ m | .load _ m | .bit m | .rmw _ m => m.usesY
  | .store r m | .cmp r m => r == .y || m.usesY
  | .incdec r _ => r == .y
  | .xfer r _ => r == .y
  | _ => false
def writesA : Kind → Bool
  | .alu _ _ | .load .a _ | .shiftA _ | .xfer _ .a | .pla => true
  | _ => false
def writesX : Kind → Bool
  | .load .x _ | .incdec .x _ | .xfer _ .x => true
  | _ => false
def writesY : Kind → Bool
  | .load .y _ | .incdec .y _ | .xfer _ .y => true
  | _ => false
def usesPtr : Kind → Bool
  | .alu _ m | .load _ m | .store _ m | .cmp _ m | .bit m | .rmw _ m => m.indirect
  | .jmpi | .rts | .rti => true
  | _ => false
def usesV : Kind → Bool
  | .alu _ m | .load _ m | .cmp _ m => m != .imm
  | .bit _ | .rmw _ _ | .rti | .pla => true
  | _ => false

def cellVS (c : Cells) (i : UInt16) : Option VS :=
  (c.find? (·.1 == i)).map (·.2)

/-- What a read at `a` may return, given the box and the global cells. -/
def readVS (rom : UInt16 → UInt8) (g : Global) (b : Box) (a : UInt16) : VS :=
  if a < 0x2000 then
    let i := a &&& 0x7FF
    match cellVS b.cells i with
    | some v => v
    | none => gAt g i
  else if 0x8000 ≤ a then .set [rom a]
  else .top

/-- The value at `i` after `wr`, if `wr` writes it: the last write wins. -/
def wrLookup : List (UInt16 × UInt8) → UInt16 → Option UInt8
  | [], _ => none
  | (a, v) :: l, i =>
    match wrLookup l i with
    | some w => some w
    | none => if i == a &&& 0x7FF then some v else none

/-- A cell whose global bound is a hypothesis about the run, so writes to it aren't checked against the bound: the VRAM buffers' offsets, whose lengths nothing in the ROM limits. Where the bound is unconstrained this changes nothing. -/
def assumedCell (i : UInt16) : Bool := i == 0x300 || i == 0x340

/-- A write is allowed: not to a protected address, within any global bound on its cell. -/
def wrOk (prot : UInt16 → Bool) (g : Global) (w : UInt16 × UInt8) : Bool :=
  !prot (w.1 &&& 0x7FF) && ((gAt g (w.1 &&& 0x7FF)).mem w.2 || assumedCell (w.1 &&& 0x7FF))

/-- Cell `c` of the successor holds: written within its set, or kept and already known to hold. -/
def cellCovered (g : Global) (b : Box) (wr : List (UInt16 × UInt8)) (c : UInt16 × VS) : Bool :=
  match wrLookup wr c.1 with
  | some v => c.2.mem v
  | none =>
    match c.2 with
    | .top => true
    | t =>
      match cellVS b.cells c.1 with
      | some v => v.sub t
      | none => (gAt g c.1).sub t

/-- As `cellCovered`, also using what the instruction just read: the cell `rd` holds `v`, unless the instruction wrote it. -/
def cellCoveredR (g : Global) (b : Box) (wr : List (UInt16 × UInt8)) (rd : Option UInt16) (v : UInt8) (c : UInt16 × VS) : Bool :=
  cellCovered g b wr c || (rd == some c.1 && (wrLookup wr c.1).isNone && c.2.mem v)

/-- The RAM cell a data read at `a` reads. -/
def readCell (k : Kind) (a : UInt16) : Option UInt16 :=
  if usesV k && a < 0x2000 then some (a &&& 0x7FF) else none

/-- `cand` allows the state `e` produces from a state of `b`, which read `v` from cell `rd`. -/
def covers (g : Global) (b : Box) (k : Kind) (e : Eff) (rd : Option UInt16) (v : UInt8) (cand : Box) : Bool :=
  cand.pc == e.regs.pc && cand.s == e.regs.s && cand.p.mem e.regs.p &&
  (if readsA k || writesA k then cand.a.mem e.regs.a else b.a.sub cand.a) &&
  (if readsX k || writesX k then cand.x.mem e.regs.x else b.x.sub cand.x) &&
  (if readsY k || writesY k then cand.y.mem e.regs.y else b.y.sub cand.y) &&
  cand.cells.all (cellCoveredR g b e.wr rd v)

/-- The table: boxes by ROM address. -/
abbrev Table := Array (List Box)

def Table.at (T : Table) (pc : UInt16) : List Box := T.getD (pc &&& 0x7FFF).toNat []

/-- The elements a register contributes to the enumeration: all its values if the instruction reads it. -/
def regList (reads : Bool) (v : VS) : List UInt8 := if reads then v.elems else [0]

/-- ALU instructions without a pointer: the access is independent of the registers and nothing is written. -/
def aluFast : Kind → Bool
  | .alu _ .imm | .alu _ .zp | .alu _ .zpx | .alu _ .zpy | .alu _ .abs | .alu _ .absx | .alu _ .absy => true
  | _ => false

/-- `p` with N, V, Z and C free. -/
def flagClosure (p : UInt8) : List UInt8 :=
  [0, 1, 2, 3, 0x40, 0x41, 0x42, 0x43, 0x80, 0x81, 0x82, 0x83, 0xC0, 0xC1, 0xC2, 0xC3].map (p &&& 0x3C ||| ·)

/-- A fast path for an ALU step whose result the successor leaves unconstrained: only the bits an ALU step cannot change
matter, so no operand needs enumerating. A compare keeps A, so its successor needs only to contain `b`'s A. -/
def aluA (b : Box) (k : Kind) (cand : Box) : Bool :=
  (match cand.a with | .top => true | _ => false) || (match k with | .alu 6 _ => b.a.sub cand.a | _ => false)

def aluCovers (g : Global) (b : Box) (k : Kind) (next : UInt16) (cand : Box) : Bool :=
  cand.pc == next && cand.s == b.s && aluA b k cand &&
  b.x.sub cand.x && b.y.sub cand.y &&
  b.p.elems.all (fun p => (flagClosure p).all cand.p.mem) &&
  cand.cells.all (cellCovered g b [])

def aluCoversFast (g : Global) (b : Box) (k : Kind) (next : UInt16) (cand : Box) : Bool :=
  cand.pc == next && cand.s == b.s && cand.cells.all (cellCovered g b []) &&
  aluA b k cand && b.x.sub cand.x && b.y.sub cand.y &&
  b.p.elems.all (fun p => (flagClosure p).all cand.p.mem)

@[csimp] theorem aluCovers_eq_fast : aluCovers = aluCoversFast := by
  funext g b k next cand
  simp only [aluCovers, aluCoversFast, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm] <;> rfl

/-- A store of A: where it goes does not depend on A or P, so only the address needs enumerating. -/
def storeFast : Kind → Bool
  | .store .a _ => true
  | _ => false

/-- The successor allows every value of A landing in cell `i`, with other cells kept. -/
def storeCovers (g : Global) (b : Box) (next i : UInt16) (cand : Box) : Bool :=
  cand.pc == next && cand.s == b.s && b.a.sub cand.a && b.x.sub cand.x && b.y.sub cand.y && b.p.sub cand.p &&
  cand.cells.all fun c => if c.1 == i then b.a.sub c.2 else cellCovered g b [] c

def storeCoversFast (g : Global) (b : Box) (next i : UInt16) (cand : Box) : Bool :=
  cand.pc == next && cand.s == b.s &&
  (cand.cells.all fun c => if c.1 == i then b.a.sub c.2 else cellCovered g b [] c) &&
  b.a.sub cand.a && b.x.sub cand.x && b.y.sub cand.y && b.p.sub cand.p

@[csimp] theorem storeCovers_eq_fast : storeCovers = storeCoversFast := by
  funext g b next i cand
  simp only [storeCovers, storeCoversFast, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm] <;> rfl

def storeOk (rom : UInt16 → UInt8) (prot : UInt16 → Bool) (g : Global) (T : Table) (b : Box) : Bool :=
  let pc := b.pc
  let k := decode (rom pc)
  let b1 := rom (pc + 1)
  let b2 := rom (pc + 2)
  storeFast k &&
  (regList (readsX k) b.x).all fun x =>
  (regList (readsY k) b.y).all fun y =>
    let r : Regs := ⟨pc, 0, x, y, b.s, 0⟩
    let pa := ptrAddrs k b1 b2 r
    (regList (usesPtr k) (readVS rom g b pa.1)).all fun lo =>
    (regList (usesPtr k) (readVS rom g b pa.2)).all fun hi =>
      let i := operandAddr k b1 b2 r lo hi &&& 0x7FF
      let next := (eval k b1 b2 r lo hi 0).regs.pc
      accessOk k b1 b2 r lo hi && !prot i && (b.a.sub (gAt g i) || assumedCell i) &&
      (T.at next).any (storeCovers g b next i)

def checkBox (rom : UInt16 → UInt8) (prot : UInt16 → Bool) (g : Global) (T : Table) (b : Box) : Bool :=
  let pc := b.pc
  let k := decode (rom pc)
  let b1 := rom (pc + 1)
  let b2 := rom (pc + 2)
  0x8000 ≤ pc && pc ≤ 0xFFF0 && k != .unknown &&
  (aluFast k && accessOk k b1 b2 ⟨pc, 0, 0, 0, b.s, 0⟩ 0 0 &&
    (T.at (eval k b1 b2 ⟨pc, 0, 0, 0, b.s, 0⟩ 0 0 0).regs.pc).any
      (aluCovers g b k (eval k b1 b2 ⟨pc, 0, 0, 0, b.s, 0⟩ 0 0 0).regs.pc) ||
  storeOk rom prot g T b ||
  (regList (readsA k) b.a).all fun a =>
  (regList (readsX k) b.x).all fun x =>
  (regList (readsY k) b.y).all fun y =>
  b.p.elems.all fun p =>
    let r : Regs := ⟨pc, a, x, y, b.s, p⟩
    let pa := ptrAddrs k b1 b2 r
    (regList (usesPtr k) (readVS rom g b pa.1)).all fun lo =>
    (regList (usesPtr k) (readVS rom g b pa.2)).all fun hi =>
    accessOk k b1 b2 r lo hi &&
    (regList (usesV k) (readVS rom g b (operandAddr k b1 b2 r lo hi))).all fun v =>
      let e := eval k b1 b2 r lo hi v
      e.regs.p &&& 4 != 0 &&
      e.wr.all (wrOk prot g) &&
      (T.at e.regs.pc).any (covers g b k e (readCell k (operandAddr k b1 b2 r lo hi)) v))

/-! ### The same test, with the per-candidate work done once

`checkBox` tries each candidate for every combination of values it enumerates, and most of `covers` doesn't depend on
those values: whether the source box's registers are inside the candidate's, and whether its cells are, for the
cells the instruction neither writes nor read. `checkBoxFast` computes those once per candidate (`pre`), lazily for
the addresses a step can reach without reading memory, and `checkBox_eq_fast` shows it's the same function, so the
compiler runs it instead. -/

/-- A candidate with what `covers` needs of it independently of the instruction's operands. -/
structure Pre where
  cand : Box
  /-- The candidate's cells that the source box doesn't already cover. -/
  bad : Cells
  sa : Bool
  sx : Bool
  sy : Bool

def pre (g : Global) (b cand : Box) : Pre :=
  ⟨cand, cand.cells.filter (fun c => !cellCovered g b [] c), b.a.sub cand.a, b.x.sub cand.x, b.y.sub cand.y⟩

/-- A written cell holds the written value. -/
def okW (wr : List (UInt16 × UInt8)) (c : UInt16 × VS) : Bool :=
  match wrLookup wr c.1 with
  | some w => c.2.mem w
  | none => true

/-- A cell not covered before holds: written, or the cell just read. -/
def okB (wr : List (UInt16 × UInt8)) (rd : Option UInt16) (v : UInt8) (c : UInt16 × VS) : Bool :=
  match wrLookup wr c.1 with
  | some _ => true
  | none => rd == some c.1 && c.2.mem v

def coversPre (b : Box) (k : Kind) (e : Eff) (rd : Option UInt16) (v : UInt8) (q : Pre) : Bool :=
  q.cand.pc == e.regs.pc && q.cand.s == e.regs.s && q.cand.p.mem e.regs.p &&
  (if readsA k || writesA k then q.cand.a.mem e.regs.a else q.sa) &&
  (if readsX k || writesX k then q.cand.x.mem e.regs.x else q.sx) &&
  (if readsY k || writesY k then q.cand.y.mem e.regs.y else q.sy) &&
  q.bad.all (okB e.wr rd v) && (e.wr.isEmpty || q.cand.cells.all (okW e.wr))

theorem cellCoveredR_split (g : Global) (b : Box) (wr : List (UInt16 × UInt8)) (rd : Option UInt16) (v : UInt8)
    (c : UInt16 × VS) :
    cellCoveredR g b wr rd v c = (okW wr c && (cellCovered g b [] c || okB wr rd v c)) := by
  unfold cellCoveredR cellCovered okW okB
  cases h : wrLookup wr c.1 <;> simp [wrLookup]

theorem cells_pre (g : Global) (b : Box) (wr : List (UInt16 × UInt8)) (rd : Option UInt16) (v : UInt8) (cs : Cells) :
    cs.all (cellCoveredR g b wr rd v) =
      ((wr.isEmpty || cs.all (okW wr)) && (cs.filter (fun c => !cellCovered g b [] c)).all (okB wr rd v)) := by
  have hw : wr.isEmpty = true → ∀ c, okW wr c = true := by
    intro he c
    have : wr = [] := List.isEmpty_iff.mp he
    subst this
    rfl
  apply Bool.eq_iff_iff.mpr
  simp only [cellCoveredR_split, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.mem_filter,
    Bool.not_eq_true']
  constructor
  · intro h
    exact ⟨Or.inr fun c hc => (h c hc).1, fun c ⟨hc, hn⟩ => by
      have := (h c hc).2
      rw [hn] at this
      simpa using this⟩
  · rintro ⟨h1, h2⟩ c hc
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | h1
      · exact hw h1 c
      · exact h1 c hc
    · cases hcc : cellCovered g b [] c
      · exact Or.inr (h2 c ⟨hc, hcc⟩)
      · exact Or.inl rfl

theorem covers_pre (g : Global) (b : Box) (k : Kind) (e : Eff) (rd : Option UInt16) (v : UInt8) (cand : Box) :
    covers g b k e rd v cand = coversPre b k e rd v (pre g b cand) := by
  simp only [covers, coversPre, pre, cells_pre, Bool.and_assoc]
  rw [Bool.and_comm (_ || _)]

/-- The addresses a step reaches without reading memory for it. -/
def nextsOf (pc : UInt16) (b1 b2 : UInt8) : List UInt16 := [pc + 1, pc + 2, pc + 3, relTarget pc b1, base b1 b2]

/-- The candidates at `n`, those whose cells `b` already covers first: they're the likely ones. -/
def preAt (g : Global) (T : Table) (b : Box) (n : UInt16) : List Pre :=
  let ps := (T.at n).map (pre g b)
  ps.filter (·.bad.isEmpty) ++ ps.filter (!·.bad.isEmpty)

theorem any_preAt (g : Global) (T : Table) (b : Box) (n : UInt16) (f : Pre → Bool) :
    (preAt g T b n).any f = ((T.at n).map (pre g b)).any f := by
  unfold preAt
  generalize (T.at n).map (pre g b) = ps
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_append, Bool.or_eq_true, List.any_eq_true, List.mem_filter]
  constructor
  · rintro (⟨x, ⟨hx, _⟩, h⟩ | ⟨x, ⟨hx, _⟩, h⟩) <;> exact ⟨x, hx, h⟩
  · rintro ⟨x, hx, h⟩
    cases hb : x.bad.isEmpty
    · exact Or.inr ⟨x, ⟨hx, by simp [hb]⟩, h⟩
    · exact Or.inl ⟨x, ⟨hx, hb⟩, h⟩

def memoOf (g : Global) (T : Table) (b : Box) (ns : List UInt16) : List (UInt16 × Thunk (List Pre)) :=
  ns.map fun n => (n, Thunk.mk fun _ => preAt g T b n)

def anyCovers (g : Global) (T : Table) (b : Box) (memo : List (UInt16 × Thunk (List Pre))) (k : Kind) (e : Eff)
    (rd : Option UInt16) (v : UInt8) : Bool :=
  match memo.lookup e.regs.pc with
  | some t => t.get.any (coversPre b k e rd v)
  | none => (T.at e.regs.pc).any (covers g b k e rd v)

theorem memoOf_lookup (g : Global) (T : Table) (b : Box) (n : UInt16) :
    ∀ (ns : List UInt16) (t : Thunk (List Pre)), (memoOf g T b ns).lookup n = some t → t.get = preAt g T b n
  | [], _, h => by simp [memoOf, List.lookup] at h
  | m :: ns, t, h => by
    simp only [memoOf, List.map_cons, List.lookup] at h
    cases hb : n == m
    · rw [hb] at h
      exact memoOf_lookup g T b n ns t h
    · rw [hb] at h
      cases h
      have : n = m := beq_iff_eq.mp hb
      subst this
      rfl

theorem anyCovers_eq (g : Global) (T : Table) (b : Box) (ns : List UInt16) (k : Kind) (e : Eff)
    (rd : Option UInt16) (v : UInt8) :
    anyCovers g T b (memoOf g T b ns) k e rd v = (T.at e.regs.pc).any (covers g b k e rd v) := by
  unfold anyCovers
  cases h : (memoOf g T b ns).lookup e.regs.pc with
  | none => rfl
  | some t =>
    simp only
    rw [memoOf_lookup g T b e.regs.pc ns t h, any_preAt, List.any_map]
    congr 1
    funext cand
    exact (covers_pre g b k e rd v cand).symm

def checkBoxFast (rom : UInt16 → UInt8) (prot : UInt16 → Bool) (g : Global) (T : Table) (b : Box) : Bool :=
  let pc := b.pc
  let k := decode (rom pc)
  let b1 := rom (pc + 1)
  let b2 := rom (pc + 2)
  let memo := memoOf g T b (nextsOf pc b1 b2)
  0x8000 ≤ pc && pc ≤ 0xFFF0 && k != .unknown &&
  (aluFast k && accessOk k b1 b2 ⟨pc, 0, 0, 0, b.s, 0⟩ 0 0 &&
    (T.at (eval k b1 b2 ⟨pc, 0, 0, 0, b.s, 0⟩ 0 0 0).regs.pc).any
      (aluCovers g b k (eval k b1 b2 ⟨pc, 0, 0, 0, b.s, 0⟩ 0 0 0).regs.pc) ||
  storeOk rom prot g T b ||
  (regList (readsA k) b.a).all fun a =>
  (regList (readsX k) b.x).all fun x =>
  (regList (readsY k) b.y).all fun y =>
  b.p.elems.all fun p =>
    let r : Regs := ⟨pc, a, x, y, b.s, p⟩
    let pa := ptrAddrs k b1 b2 r
    (regList (usesPtr k) (readVS rom g b pa.1)).all fun lo =>
    (regList (usesPtr k) (readVS rom g b pa.2)).all fun hi =>
    accessOk k b1 b2 r lo hi &&
    (regList (usesV k) (readVS rom g b (operandAddr k b1 b2 r lo hi))).all fun v =>
      let e := eval k b1 b2 r lo hi v
      e.regs.p &&& 4 != 0 &&
      e.wr.all (wrOk prot g) &&
      anyCovers g T b memo k e (readCell k (operandAddr k b1 b2 r lo hi)) v)

@[csimp] theorem checkBox_eq_fast : checkBox = checkBoxFast := by
  funext rom prot g T b
  simp only [checkBox, checkBoxFast, anyCovers_eq]

/-- Every box at address `n` is at `n`, in ROM, carries the I flag, and steps inside the table or sits at an exit. -/
def check (rom : UInt16 → UInt8) (exit prot : UInt16 → Bool) (g : Global) (T : Table) : Bool :=
  (List.range 0x8000).all fun n =>
    (T.getD n []).all fun b =>
      (b.pc &&& 0x7FFF).toNat == n && 0x8000 ≤ b.pc &&
      (b.p.elems.all (fun p => p &&& 4 != 0)) &&
      (exit b.pc || checkBox rom prot g T b)

/-- `e` is contained in `c`. -/
def Box.le (g : Global) (e c : Box) : Bool :=
  c.pc == e.pc && c.s == e.s && e.a.sub c.a && e.x.sub c.x && e.y.sub c.y && e.p.sub c.p &&
  c.cells.all (cellCovered g e [])

/-- The table has a box containing `e`. -/
def entryIn (g : Global) (T : Table) (e : Box) : Bool := (T.at e.pc).any (Box.le g e)

/-- The cartridge's PRG as the CPU reads it. -/
def romOf (prg : ByteArray) : UInt16 → UInt8 := fun a => prg.get! (a &&& 0x7FFF).toNat

end Smb.Abs
