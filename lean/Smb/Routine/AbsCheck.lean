import Smb.Abs.Check
import Smb.Routine.AbsSem

/-!
# The box checker is sound

`inv_step`: if `check` accepts a table, a plain-machine state some box allows steps to a state some box allows, unless it
sits at an exit. Along the way the global cell bounds keep holding, and protected RAM keeps its values. `inv_runTo` extends
this to any bounded run. The table can come from anywhere, since only `check` is trusted.
-/
namespace Smb.Abs
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

/-! ## Independence of what an instruction does not read -/

local macro "agree_tac" : tactic => `(tactic|
  simp [eval, ptrAddrs, ptrCells, accessOk, operandAddr, ea, regOf, readsA, readsX, readsY, writesA, writesX, writesY,
    usesPtr, usesV, Mode.usesX, Mode.usesY, Mode.indirect] <;> first | rfl | congr)

theorem eval_agree (k : Kind) (b1 b2 : UInt8) (pc : UInt16) (a x y s p lo hi v : UInt8) :
    let r : Regs := ⟨pc, a, x, y, s, p⟩
    let r0 : Regs := ⟨pc, if readsA k then a else 0, if readsX k then x else 0, if readsY k then y else 0, s, p⟩
    let lo0 := if usesPtr k then lo else 0
    let hi0 := if usesPtr k then hi else 0
    let v0 := if usesV k then v else 0
    ptrAddrs k b1 b2 r0 = ptrAddrs k b1 b2 r ∧
    accessOk k b1 b2 r0 lo0 hi0 = accessOk k b1 b2 r lo hi ∧
    operandAddr k b1 b2 r0 lo0 hi0 = operandAddr k b1 b2 r lo hi ∧
    (eval k b1 b2 r0 lo0 hi0 v0).wr = (eval k b1 b2 r lo hi v).wr ∧
    (eval k b1 b2 r0 lo0 hi0 v0).regs.pc = (eval k b1 b2 r lo hi v).regs.pc ∧
    (eval k b1 b2 r0 lo0 hi0 v0).regs.s = (eval k b1 b2 r lo hi v).regs.s ∧
    (eval k b1 b2 r0 lo0 hi0 v0).regs.p = (eval k b1 b2 r lo hi v).regs.p ∧
    (if readsA k || writesA k then (eval k b1 b2 r0 lo0 hi0 v0).regs.a = (eval k b1 b2 r lo hi v).regs.a
      else (eval k b1 b2 r lo hi v).regs.a = a) ∧
    (if readsX k || writesX k then (eval k b1 b2 r0 lo0 hi0 v0).regs.x = (eval k b1 b2 r lo hi v).regs.x
      else (eval k b1 b2 r lo hi v).regs.x = x) ∧
    (if readsY k || writesY k then (eval k b1 b2 r0 lo0 hi0 v0).regs.y = (eval k b1 b2 r lo hi v).regs.y
      else (eval k b1 b2 r lo hi v).regs.y = y) := by
  cases k with
  | alu k m => cases m <;> agree_tac
  | load r m => cases r <;> cases m <;> agree_tac
  | store r m => cases r <;> cases m <;> agree_tac
  | cmp r m => cases r <;> cases m <;> agree_tac
  | bit m => cases m <;> agree_tac
  | rmw k m => cases m <;> agree_tac
  | shiftA k => agree_tac
  | incdec r d => cases r <;> agree_tac
  | xfer a b => cases a <;> cases b <;> agree_tac
  | setp c t => agree_tac
  | branch m w => agree_tac
  | jmp => agree_tac
  | jmpi => agree_tac
  | jsr => agree_tac
  | rts => agree_tac
  | rti => agree_tac
  | pha => agree_tac
  | pla => agree_tac
  | txs => agree_tac
  | unknown => agree_tac

/-! ## Value sets -/

theorem mem_allBytes (v : UInt8) : v ∈ allBytes := by
  have key : ∀ n : Fin 256, UInt8.ofNat n.val ∈ allBytes := by decide
  simpa using key ⟨v.toNat, v.toNat_lt⟩

theorem VS.mem_elems {t : VS} {v : UInt8} (h : t.mem v = true) : v ∈ t.elems := by
  cases t with
  | top => exact mem_allBytes v
  | set l => simpa [VS.mem, VS.elems] using h

theorem VS.sub_sound {t u : VS} {v : UInt8} (hs : t.sub u = true) (h : t.mem v = true) : u.mem v = true := by
  cases u with
  | top => rfl
  | set l =>
    cases t with
    | top => simp [VS.sub] at hs
    | set m =>
      simp only [VS.sub, List.all_eq_true] at hs
      exact hs v (by simpa [VS.mem] using h)

theorem cellVS_sound {c : Cells} {i : UInt16} {t : VS} (h : cellVS c i = some t) : (i, t) ∈ c := by
  simp only [cellVS, Option.map_eq_some_iff] at h
  obtain ⟨⟨j, u⟩, hf, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some hf
  have he := List.find?_some hf
  simp only [beq_iff_eq] at he
  subst he
  exact hm

/-! ## What a box means -/

/-- The machine's ROM holds the code `rom` gives. -/
def Code (rom : UInt16 → UInt8) (s : Plain) : Prop := ∀ a, 0x8000 ≤ a → s.prg (a &&& 0x7FFF) = rom a

/-- `s` is allowed by box `b`, under the global cell bounds `g`, with protected RAM still as in `ram0`. -/
structure Holds (prot : UInt16 → Bool) (g : Global) (ram0 : UInt16 → UInt8) (b : Box) (s : Plain) : Prop where
  pc : s.regs.pc = b.pc
  sp : s.regs.s = b.s
  a : b.a.mem s.regs.a = true
  x : b.x.mem s.regs.x = true
  y : b.y.mem s.regs.y = true
  p : b.p.mem s.regs.p = true
  i : s.regs.p &&& 4 ≠ 0
  bad : s.bad = false
  cells : ∀ c ∈ b.cells, c.2.mem (s.ram c.1) = true
  glob : ∀ i, (gAt g i).mem (s.ram i) = true
  frame : ∀ i, prot i = true → s.ram i = ram0 i

def Inv (prot : UInt16 → Bool) (g : Global) (ram0 : UInt16 → UInt8) (T : Table) (s : Plain) : Prop :=
  ∃ b ∈ T.at s.regs.pc, Holds prot g ram0 b s

/-- The bound is unconstrained, as something `native_decide` can run. -/
def topB : VS → Bool
  | .top => true
  | _ => false

theorem eq_top_of_topB {v : VS} (h : topB v = true) : v = .top := by
  cases v with
  | top => rfl
  | set l => simp [topB] at h

/-- The assumed cells are within their bounds. -/
def AssumedOk (g : Global) (f : UInt16 → UInt8) : Prop := ∀ i, assumedCell i = true → (gAt g i).mem (f i) = true

/-- `Holds`, except for the bounds on the assumed cells, which is what a step can show by itself. -/
structure HoldsP (prot : UInt16 → Bool) (g : Global) (ram0 : UInt16 → UInt8) (b : Box) (s : Plain) : Prop where
  pc : s.regs.pc = b.pc
  sp : s.regs.s = b.s
  a : b.a.mem s.regs.a = true
  x : b.x.mem s.regs.x = true
  y : b.y.mem s.regs.y = true
  p : b.p.mem s.regs.p = true
  i : s.regs.p &&& 4 ≠ 0
  bad : s.bad = false
  cells : ∀ c ∈ b.cells, c.2.mem (s.ram c.1) = true
  glob : ∀ i, assumedCell i = false → (gAt g i).mem (s.ram i) = true
  frame : ∀ i, prot i = true → s.ram i = ram0 i

theorem Holds.toP {prot g ram0} {b : Box} {s : Plain} (h : Holds prot g ram0 b s) : HoldsP prot g ram0 b s :=
  ⟨h.pc, h.sp, h.a, h.x, h.y, h.p, h.i, h.bad, h.cells, fun i _ => h.glob i, h.frame⟩

/-- The run's hypothesis supplies the assumed cell's bound. -/
theorem HoldsP.holds {prot g ram0} {b : Box} {s : Plain} (h : HoldsP prot g ram0 b s) (ha : AssumedOk g s.ram) :
    Holds prot g ram0 b s :=
  ⟨h.pc, h.sp, h.a, h.x, h.y, h.p, h.i, h.bad, h.cells, (fun i => by
    cases hi : assumedCell i with
    | false => exact h.glob i hi
    | true => exact ha i hi), h.frame⟩

theorem assumedOk_of_top {g : Global} (h300 : gAt g 0x300 = .top) (h340 : gAt g 0x340 = .top) (f : UInt16 → UInt8) : AssumedOk g f := by
  intro i hi
  have h : i = 0x300 ∨ i = 0x340 := by simpa [assumedCell] using hi
  rcases h with rfl | rfl
  · rw [h300]; rfl
  · rw [h340]; rfl

def InvP (prot : UInt16 → Bool) (g : Global) (ram0 : UInt16 → UInt8) (T : Table) (s : Plain) : Prop :=
  ∃ b ∈ T.at s.regs.pc, HoldsP prot g ram0 b s

theorem readVS_sound {rom : UInt16 → UInt8} {prot g ram0} {b : Box} {s : Plain} (hc : Code rom s)
    (h : Holds prot g ram0 b s) (a : UInt16) :
    (readVS rom g b a).mem (Plain.memRead s.ram s.prg a) = true := by
  unfold readVS Plain.memRead Plain.inRam
  by_cases h1 : a < 0x2000
  · simp only [h1, if_true, decide_true, cond_true]
    cases hb : cellVS b.cells (a &&& 0x7FF) with
    | some t => exact h.cells _ (cellVS_sound hb)
    | none => exact h.glob _
  · simp only [h1, if_false, decide_false, cond_false]
    by_cases h2 : 0x8000 ≤ a
    · simp only [h2, if_true, hc a h2, VS.mem, List.contains_cons, beq_self_eq_true, Bool.true_or, List.contains_nil]
    · simp only [h2, if_false]; rfl

theorem regList_mem {reads : Bool} {t : VS} {v : UInt8} (h : t.mem v = true) :
    (if reads then v else 0) ∈ regList reads t := by
  cases reads <;> simp [regList, VS.mem_elems h]

/-! ## Writes -/

theorem applyW_nil (ram : UInt16 → UInt8) : applyW ram [] = ram := rfl

theorem applyW_lookup (wr : List (UInt16 × UInt8)) (ram : UInt16 → UInt8) (i : UInt16) :
    applyW ram wr i = (wrLookup wr i).getD (ram i) := by
  induction wr generalizing ram with
  | nil => rfl
  | cons w l ih =>
    obtain ⟨a, v⟩ := w
    simp only [applyW, wrLookup, ih]
    cases wrLookup l i with
    | some w => rfl
    | none =>
      simp only [Option.getD_none]
      by_cases h : i == a &&& 0x7FF <;> simp [h]

/-- A written value in `wr` came from a write that `wrOk` allowed. -/
theorem wrLookup_ok {prot : UInt16 → Bool} {g : Global} {wr : List (UInt16 × UInt8)} {i : UInt16} {v : UInt8}
    (hok : wr.all (wrOk prot g) = true) (h : wrLookup wr i = some v) :
    prot i = false ∧ ((gAt g i).mem v = true ∨ assumedCell i = true) := by
  induction wr with
  | nil => simp [wrLookup] at h
  | cons w l ih =>
    obtain ⟨a, u⟩ := w
    simp only [List.all_cons, Bool.and_eq_true] at hok
    simp only [wrLookup] at h
    cases hl : wrLookup l i with
    | some w =>
      simp only [hl, Option.some.injEq] at h
      subst h
      exact ih hok.2 hl
    | none =>
      simp only [hl] at h
      by_cases he : i == a &&& 0x7FF
      · simp only [he, if_true, Option.some.injEq] at h
        subst h
        have hi : i = a &&& 0x7FF := by simpa using he
        have hw := hok.1
        simp only [wrOk, Bool.and_eq_true] at hw
        subst hi
        exact ⟨by simpa using hw.1, by simpa using hw.2⟩
      · simp [he] at h

theorem cellCovered_sound {prot g ram0} {b : Box} {s : Plain} (h : Holds prot g ram0 b s)
    {wr : List (UInt16 × UInt8)} {c : UInt16 × VS} (hc : cellCovered g b wr c = true) :
    c.2.mem (applyW s.ram wr c.1) = true := by
  rw [applyW_lookup]
  unfold cellCovered at hc
  cases hl : wrLookup wr c.1 with
  | some v => simpa [hl] using hc
  | none =>
    simp only [hl, Option.getD_none] at hc ⊢
    obtain ⟨i, t⟩ := c
    cases t with
    | top => rfl
    | set l =>
      simp only at hc ⊢
      cases hb : cellVS b.cells i with
      | some u =>
        simp only [hb] at hc
        exact VS.sub_sound hc (h.cells _ (cellVS_sound hb))
      | none =>
        simp only [hb] at hc
        exact VS.sub_sound hc (h.glob _)

/-- What an instruction read: a cell it did not write still holds the value it read. -/
theorem cellCoveredR_sound {prot g ram0} {b : Box} {s : Plain} (h : Holds prot g ram0 b s)
    {k : Kind} {wr : List (UInt16 × UInt8)} {a : UInt16} {v : UInt8} {c : UInt16 × VS}
    (hv : usesV k = true → v = Plain.memRead s.ram s.prg a)
    (hc : cellCoveredR g b wr (readCell k a) v c = true) :
    c.2.mem (applyW s.ram wr c.1) = true := by
  simp only [cellCoveredR, Bool.or_eq_true, Bool.and_eq_true] at hc
  rcases hc with hc | ⟨⟨hrd, hnone⟩, hmem⟩
  · exact cellCovered_sound h hc
  · have hrd' : readCell k a = some c.1 := by simpa using hrd
    simp only [readCell] at hrd'
    split at hrd'
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      have he : a &&& 0x7FF = c.1 := by simpa using hrd'
      rw [applyW_lookup]
      have hn : wrLookup wr c.1 = none := by simpa using hnone
      rw [hn, Option.getD_none]
      have hread : v = s.ram c.1 := by
        rw [hv hcond.1, ← he]
        simp [Plain.memRead, Plain.inRam, hcond.2]
      rw [← hread]
      exact hmem
    · cases hrd'

theorem table_at_lt (pc : UInt16) : (pc &&& 0x7FFF).toNat < 0x8000 := by
  have : pc &&& 0x7FFF < 0x8000 := by bv_decide (config := { enums := false })
  exact this

/-! ## The ALU fast path -/

theorem alu_flags (k : Nat) (a m p : UInt8) : (aluFn k a m p).2 &&& 0x3C = p &&& 0x3C := by
  unfold aluFn nz
  simp only [CPU.FC, CPU.FV, CPU.FN, CPU.FZ]
  split <;> (try split) <;> simp only [] <;> bv_decide (config := { enums := false })

theorem flag_mem (q : UInt8) : q &&& 0xC3 ∈ ([0, 1, 2, 3, 0x40, 0x41, 0x42, 0x43, 0x80, 0x81, 0x82, 0x83, 0xC0, 0xC1, 0xC2, 0xC3] : List UInt8) := by
  have key : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0xC3 ∈ ([0, 1, 2, 3, 0x40, 0x41, 0x42, 0x43, 0x80, 0x81, 0x82, 0x83, 0xC0, 0xC1, 0xC2, 0xC3] : List UInt8) := by decide
  simpa using key ⟨q.toNat, q.toNat_lt⟩

theorem mem_closure {p q : UInt8} (h : q &&& 0x3C = p &&& 0x3C) : q ∈ flagClosure p := by
  simp only [flagClosure, List.mem_map]
  refine ⟨q &&& 0xC3, flag_mem q, ?_⟩
  bv_decide (config := { enums := false })

theorem aluA_sound {b cand : Box} {n : Nat} {m : Mode} {a w p : UInt8}
    (h : aluA b (.alu n m) cand = true) (ha : b.a.mem a = true) : cand.a.mem (aluFn n a w p).1 = true := by
  by_cases h6 : n = 6
  · subst h6
    rcases (Bool.or_eq_true _ _).mp h with h1 | h1
    · cases hc : cand.a with
      | top => rfl
      | set l => simp [hc] at h1
    · have h2 : b.a.sub cand.a = true := h1
      simpa [aluFn] using VS.sub_sound h2 ha
  · cases hc : cand.a with
    | top => rfl
    | set l =>
      have h3 : (match Kind.alu n m with | .alu 6 _ => b.a.sub cand.a | _ => false) = false := by
        split
        · rename_i hk; injection hk with h4 _; exact absurd h4 h6
        · rfl
      rcases (Bool.or_eq_true _ _).mp h with h1 | h1
      · simp [hc] at h1
      · exact absurd (h3.symm.trans h1) (by simp)

/-- One step taken by the fast path. -/
theorem inv_step_fast {rom : UInt16 → UInt8} {prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    {s : Plain} {b : Box} (hc : Code rom s) (hb : Holds prot g ram0 b s) (hpcb : s.regs.pc = b.pc)
    (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0) (hk : ¬decode (rom s.regs.pc) = Kind.unknown)
    (hfast : (aluFast (decode (rom s.regs.pc)) = true ∧
        accessOk (decode (rom s.regs.pc)) (rom (s.regs.pc + 1)) (rom (s.regs.pc + 2)) ⟨s.regs.pc, 0, 0, 0, b.s, 0⟩ 0 0 = true) ∧
      ∃ cand, cand ∈ T.at (eval (decode (rom s.regs.pc)) (rom (s.regs.pc + 1)) (rom (s.regs.pc + 2)) ⟨s.regs.pc, 0, 0, 0, b.s, 0⟩ 0 0 0).regs.pc ∧
        aluCovers g b (decode (rom s.regs.pc)) (eval (decode (rom s.regs.pc)) (rom (s.regs.pc + 1)) (rom (s.regs.pc + 2)) ⟨s.regs.pc, 0, 0, 0, b.s, 0⟩ 0 0 0).regs.pc cand = true) :
    Code rom (CPU.step.run s).2 ∧ Inv prot g ram0 T (CPU.step.run s).2 := by
  obtain ⟨⟨hal, hacc⟩, cand, hcm, hcov⟩ := hfast
  have hprg : s.prg (s.regs.pc &&& 0x7FFF) = rom s.regs.pc := hc _ h0
  have hb1 : b1Of s = rom (s.regs.pc + 1) := hc _ (by bv_decide (config := { enums := false }))
  have hb2 : b2Of s = rom (s.regs.pc + 2) := hc _ (by bv_decide (config := { enums := false }))
  have hkk' : decode (s.prg (s.regs.pc &&& 0x7FFF)) = decode (rom s.regs.pc) := by rw [hprg]
  generalize hkd : decode (rom s.regs.pc) = k at *
  generalize rom (s.regs.pc + 1) = b1 at *
  generalize rom (s.regs.pc + 2) = b2 at *
  have hsp := hb.sp
  obtain ⟨⟨pc, a, x, y, b.s, p⟩, ram, prg, cyc, bad⟩ := s
  simp only at hcm hcov hacc h0 h2 hb1 hb2 hkk' hpcb hsp
  subst hsp
  -- an ALU instruction: its shape
  cases k with
  | alu n m =>
    have hmode : (m = .imm ∨ m = .zp ∨ m = .zpx ∨ m = .zpy ∨ m = .abs ∨ m = .absx ∨ m = .absy) := by
      cases m <;> simp_all [aluFast]
    have hrun := step_eval ⟨⟨pc, a, x, y, b.s, p⟩, ram, prg, cyc, bad⟩ h0 h2 hb.i
      (by rw [hkk']; exact hk)
      (by
        rw [hkk', hb1, hb2]
        rcases hmode with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [accessOk] using hacc)
      (by
        rw [hkk']
        simp only [evalS, hb1, hb2, eval]
        have hf := alu_flags n a (if m = .imm then b1 else vOf ⟨⟨pc, a, x, y, b.s, p⟩, ram, prg, cyc, bad⟩ (Kind.alu n m)) p
        have hi := hb.i
        simp only at hi
        intro h
        apply hi
        bv_decide (config := { enums := false }))
    rw [hkk'] at hrun
    obtain ⟨hregs, hprgt, hramt, hbadt⟩ := hrun
    simp only [evalS, hb1, hb2, eval] at hregs hramt
    simp only [eval] at hcm hcov
    simp only [aluCovers, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcov
    obtain ⟨⟨⟨⟨⟨⟨hcpc, hcs⟩, hca⟩, hcx⟩, hcy⟩, hcp⟩, hcc⟩ := hcov
    have hf := alu_flags n a (if m = .imm then b1 else vOf ⟨⟨pc, a, x, y, b.s, p⟩, ram, prg, cyc, bad⟩ (Kind.alu n m)) p
    refine ⟨?_, cand, ?_, ?_⟩
    · intro a' ha'
      rw [hprgt]
      exact hc a' ha'
    · rw [hregs]; exact hcm
    · exact {
        pc := by rw [hregs]; exact hcpc.symm
        sp := by rw [hregs]; exact hcs.symm
        a := by
          rw [hregs]
          exact aluA_sound hca hb.a
        x := by rw [hregs]; exact VS.sub_sound hcx hb.x
        y := by rw [hregs]; exact VS.sub_sound hcy hb.y
        p := by
          rw [hregs]
          exact hcp p (VS.mem_elems hb.p) _ (mem_closure hf)
        i := by
          rw [hregs]
          have hi := hb.i
          simp only at hi ⊢
          intro h
          apply hi
          bv_decide (config := { enums := false })
        bad := by rw [hbadt]; exact hb.bad
        cells := by
          intro c hcin
          rw [hramt]
          exact cellCovered_sound hb (hcc c hcin)
        glob := by
          intro i
          rw [hramt]
          exact hb.glob i
        frame := by
          intro i hpi
          rw [hramt]
          exact hb.frame i hpi }
  | _ => simp [aluFast] at hal

/-! ## The store fast path -/

theorem store_indep (m : Mode) (b1 b2 : UInt8) (pc : UInt16) (a x y s p lo hi v : UInt8) :
    let k := Kind.store .a m
    let r : Regs := ⟨pc, a, x, y, s, p⟩
    let r1 : Regs := ⟨pc, 0, if readsX k then x else 0, if readsY k then y else 0, s, 0⟩
    let lo0 := if usesPtr k then lo else 0
    let hi0 := if usesPtr k then hi else 0
    ptrAddrs k b1 b2 r1 = ptrAddrs k b1 b2 r ∧
    accessOk k b1 b2 r1 lo0 hi0 = accessOk k b1 b2 r lo hi ∧
    operandAddr k b1 b2 r1 lo0 hi0 = operandAddr k b1 b2 r lo hi ∧
    (eval k b1 b2 r lo hi v).regs = ⟨pc + m.size, a, x, y, s, p⟩ ∧
    (eval k b1 b2 r lo hi v).wr = [(operandAddr k b1 b2 r lo hi, a)] ∧
    (eval k b1 b2 r1 lo0 hi0 0).regs.pc = pc + m.size := by
  cases m <;> agree_tac

/-- One step taken by the store fast path. -/
theorem inv_step_store {rom : UInt16 → UInt8} {prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    {s : Plain} {b : Box} (hc : Code rom s) (hb : Holds prot g ram0 b s) (hpcb : s.regs.pc = b.pc)
    (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0) (hk : ¬decode (rom s.regs.pc) = Kind.unknown)
    (hstore : storeOk rom prot g T b = true) :
    Code rom (CPU.step.run s).2 ∧ InvP prot g ram0 T (CPU.step.run s).2 := by
  unfold storeOk at hstore
  simp only [← hpcb, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.not_eq_true'] at hstore
  obtain ⟨hsf, hall⟩ := hstore
  have hprg : s.prg (s.regs.pc &&& 0x7FFF) = rom s.regs.pc := hc _ h0
  have hb1 : b1Of s = rom (s.regs.pc + 1) := hc _ (by bv_decide (config := { enums := false }))
  have hb2 : b2Of s = rom (s.regs.pc + 2) := hc _ (by bv_decide (config := { enums := false }))
  have hkk' : decode (s.prg (s.regs.pc &&& 0x7FFF)) = decode (rom s.regs.pc) := by rw [hprg]
  generalize hkd : decode (rom s.regs.pc) = k at *
  generalize rom (s.regs.pc + 1) = b1 at *
  generalize rom (s.regs.pc + 2) = b2 at *
  have hsp := hb.sp
  obtain ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ := s
  simp only at hall h0 h2 hb1 hb2 hkk' hpcb hsp
  subst hsp
  cases k with
  | store rg m =>
    cases rg with
    | a =>
      have hind := store_indep m b1 b2 pc a x y b.s p
        (loOf ⟨⟨pc, a, x, y, b.s, p⟩, ram, prg, cyc, bad⟩ (Kind.store .a m))
        (hiOf ⟨⟨pc, a, x, y, b.s, p⟩, ram, prg, cyc, bad⟩ (Kind.store .a m))
        (vOf ⟨⟨pc, a, x, y, b.s, p⟩, ram, prg, cyc, bad⟩ (Kind.store .a m))
      dsimp only at hind
      obtain ⟨gptr, gacc, gop, gregs, gwr, gnext⟩ := hind
      have hread := fun a' => readVS_sound hc hb a'
      simp only at hread
      have hl := hall (if readsX (Kind.store .a m) then x else 0) (regList_mem hb.x)
        (if readsY (Kind.store .a m) then y else 0) (regList_mem hb.y)
        (if usesPtr (Kind.store .a m) then loOf ⟨⟨pc, a, x, y, b.s, p⟩, ram, prg, cyc, bad⟩ (Kind.store .a m) else 0)
        (by
          rw [gptr]
          apply regList_mem
          simp only [loOf, mr, b1Of, b2Of] at hb1 hb2 ⊢
          rw [hb1, hb2]
          exact hread _)
        (if usesPtr (Kind.store .a m) then hiOf ⟨⟨pc, a, x, y, b.s, p⟩, ram, prg, cyc, bad⟩ (Kind.store .a m) else 0)
        (by
          rw [gptr]
          apply regList_mem
          simp only [hiOf, mr, b1Of, b2Of] at hb1 hb2 ⊢
          rw [hb1, hb2]
          exact hread _)
      obtain ⟨⟨⟨hacc, hnp⟩, hga⟩, cand, hcm, hcov⟩ := hl
      rw [gop] at hnp hga hcov
      rw [gacc] at hacc
      rw [gnext] at hcm hcov
      have hrun := step_eval ⟨⟨pc, a, x, y, b.s, p⟩, ram, prg, cyc, bad⟩ h0 h2 hb.i
        (by rw [hkk']; exact hk)
        (by rw [hkk', hb1, hb2]; simpa only [loOf, hiOf, mr, b1Of, b2Of, hb1, hb2] using hacc)
        (by
          rw [hkk']
          simp only [evalS, hb1, hb2]
          rw [gregs]
          exact hb.i)
      rw [hkk'] at hrun
      obtain ⟨hregs, hprgt, hramt, hbadt⟩ := hrun
      simp only [evalS, hb1, hb2] at hregs hramt
      rw [gregs] at hregs
      rw [gwr] at hramt
      simp only [storeCovers, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcov
      obtain ⟨⟨⟨⟨⟨⟨hcpc, hcs⟩, hca⟩, hcx⟩, hcy⟩, hcp⟩, hcc⟩ := hcov
      generalize hI : operandAddr (Kind.store .a m) b1 b2 ⟨pc, a, x, y, b.s, p⟩
        (loOf ⟨⟨pc, a, x, y, b.s, p⟩, ram, prg, cyc, bad⟩ (Kind.store .a m))
        (hiOf ⟨⟨pc, a, x, y, b.s, p⟩, ram, prg, cyc, bad⟩ (Kind.store .a m)) &&& 2047 = i at *
      have hlook (j : UInt16) : (CPU.step.run ({ regs := ⟨pc, a, x, y, b.s, p⟩, ram, prg, cyc, bad } : Plain)).2.ram j =
          if j == i then a else ram j := by
        rw [hramt, applyW_lookup]
        by_cases he : j == i
        · have hji : j = i := by simpa using he
          subst hji
          simp only [wrLookup, he, if_true, Option.getD_some]
          simp [← hI]
        · have : ¬ (j == (operandAddr (Kind.store .a m) b1 b2 ⟨pc, a, x, y, b.s, p⟩
              (loOf ⟨⟨pc, a, x, y, b.s, p⟩, ram, prg, cyc, bad⟩ (Kind.store .a m))
              (hiOf ⟨⟨pc, a, x, y, b.s, p⟩, ram, prg, cyc, bad⟩ (Kind.store .a m)) &&& 0x7FF)) = true := by
            rw [show (0x7FF : UInt16) = 2047 from rfl, hI]; exact he
          simp [wrLookup, this, he]
      refine ⟨?_, cand, ?_, ?_⟩
      · intro a' ha'
        rw [hprgt]
        exact hc a' ha'
      · rw [hregs]; exact hcm
      · exact {
          pc := by rw [hregs]; exact hcpc.symm
          sp := by rw [hregs]; exact hcs.symm
          a := by rw [hregs]; exact VS.sub_sound hca hb.a
          x := by rw [hregs]; exact VS.sub_sound hcx hb.x
          y := by rw [hregs]; exact VS.sub_sound hcy hb.y
          p := by rw [hregs]; exact VS.sub_sound hcp hb.p
          i := by rw [hregs]; exact hb.i
          bad := by rw [hbadt]; exact hb.bad
          cells := by
            intro c hcin
            rw [hlook]
            have h := hcc c hcin
            by_cases he : c.1 = i
            · have h' : b.a.sub c.2 = true := by simpa [he] using h
              simp only [he, beq_self_eq_true, if_true]
              exact VS.sub_sound h' hb.a
            · have h' : cellCovered g b [] c = true := by simpa [he] using h
              have hne : (c.1 == i) = false := by simpa using he
              simp only [hne, Bool.false_eq_true, if_false]
              have hk := cellCovered_sound hb h'
              simpa [applyW] using hk
          glob := by
            intro j hja
            rw [hlook]
            by_cases he : j == i
            · have hji : j = i := by simpa using he
              subst hji
              simp only [he, if_true]
              rcases (Bool.or_eq_true _ _).mp hga with hga | hga
              · exact VS.sub_sound hga hb.a
              · rw [hja] at hga; cases hga
            · simp only [he, if_false]; exact hb.glob j
          frame := by
            intro j hpj
            rw [hlook]
            by_cases he : j == i
            · have hji : j = i := by simpa using he
              subst hji
              rw [hpj] at hnp
              cases hnp
            · simp only [he, if_false]; exact hb.frame j hpj }
    | x => simp [storeFast] at hsf
    | y => simp [storeFast] at hsf
  | _ => simp [storeFast] at hsf

/-- One box the checker accepted: a state it allows steps into the table. -/
theorem inv_step_box {rom : UInt16 → UInt8} {prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    {s : Plain} {b : Box} (hck : checkBox rom prot g T b = true) (hc : Code rom s) (hb : Holds prot g ram0 b s) :
    Code rom (CPU.step.run s).2 ∧ InvP prot g ram0 T (CPU.step.run s).2 := by
  have hpcb := hb.pc
  unfold checkBox at hck
  simp only [← hpcb, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, List.any_eq_true] at hck
  obtain ⟨⟨⟨h0, h2⟩, hk⟩, hall⟩ := hck
  rcases hall with (hfast | hstore) | hall
  · obtain ⟨h1, c, h2', h3⟩ := inv_step_fast hc hb hpcb h0 h2 hk hfast
    exact ⟨h1, c, h2', h3.toP⟩
  · exact inv_step_store hc hb hpcb h0 h2 hk hstore
  -- the ROM bytes the step reads
  have hprg : s.prg (s.regs.pc &&& 0x7FFF) = rom s.regs.pc := hc _ h0
  have hb1 : b1Of s = rom (s.regs.pc + 1) := hc _ (by bv_decide (config := { enums := false }))
  have hb2 : b2Of s = rom (s.regs.pc + 2) := hc _ (by bv_decide (config := { enums := false }))
  generalize hkk : decode (rom s.regs.pc) = k at hk hall
  have hkk' : decode (s.prg (s.regs.pc &&& 0x7FFF)) = k := by rw [hprg, hkk]
  generalize hB1 : rom (s.regs.pc + 1) = b1 at hall hb1
  generalize hB2 : rom (s.regs.pc + 2) = b2 at hall hb2
  obtain ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ := s
  simp only at hall hb1 hb2 hpcb hkk'
  have hsp : b.s = sp := hb.sp.symm
  rw [hsp] at hall
  have hagree := eval_agree k b1 b2 pc a x y sp p
    (loOf ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ k) (hiOf ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ k)
    (vOf ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ k)
  dsimp only at hagree
  obtain ⟨gptr, gacc, gop, gwr, gpc, gs, gp, ga, gx, gy⟩ := hagree
  have hread := fun a' => readVS_sound hc hb a'
  simp only at hread
  have hl1 := hall (if readsA k then a else 0) (regList_mem hb.a) (if readsX k then x else 0) (regList_mem hb.x)
    (if readsY k then y else 0) (regList_mem hb.y) p (VS.mem_elems hb.p)
    (if usesPtr k then loOf ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ k else 0)
    (by
      rw [gptr]
      apply regList_mem
      simp only [loOf, mr, b1Of, b2Of] at hb1 hb2 ⊢
      rw [hb1, hb2]
      exact hread _)
    (if usesPtr k then hiOf ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ k else 0)
    (by
      rw [gptr]
      apply regList_mem
      simp only [hiOf, mr, b1Of, b2Of] at hb1 hb2 ⊢
      rw [hb1, hb2]
      exact hread _)
  obtain ⟨hacc, hl2⟩ := hl1
  rw [gacc] at hacc
  have hl3 := hl2 (if usesV k then vOf ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ k else 0)
    (by
      rw [gop]
      apply regList_mem
      simp only [vOf, loOf, hiOf, mr, b1Of, b2Of] at hb1 hb2 ⊢
      rw [hb1, hb2]
      exact hread _)
  obtain ⟨⟨hI', hw⟩, cand, hcm, hcov⟩ := hl3
  rw [gpc] at hcm
  rw [gwr] at hw
  rw [gp] at hI'
  -- the actual step
  have hrun := step_eval ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ h0 h2 hb.i
    (by rw [hkk']; exact hk)
    (by rw [hkk', hb1, hb2]; simpa only [loOf, hiOf, mr, b1Of, b2Of, hb1, hb2] using hacc)
    (by
      rw [hkk']
      simp only [evalS, hb1, hb2]
      exact hI')
  rw [hkk'] at hrun
  obtain ⟨hregs, hprgt, hramt, hbadt⟩ := hrun
  simp only [evalS, hb1, hb2] at hregs hramt
  simp only [covers, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcov
  obtain ⟨⟨⟨⟨⟨⟨hcpc, hcs⟩, hcp⟩, hca⟩, hcx⟩, hcy⟩, hcc⟩ := hcov
  rw [gpc] at hcpc
  rw [gs] at hcs
  rw [gp] at hcp
  rw [gwr] at hcc
  have hreg : ∀ {r w : Bool} {t u : VS} {e0 e v : UInt8}, (if r || w then u.mem e0 else t.sub u) = true →
      (if r || w then e0 = e else e = v) → t.mem v = true → u.mem e = true := by
    intro r w t u e0 e v h1 h2 h3
    by_cases hr : (r || w) = true
    · simp only [hr, if_true] at h1 h2
      rw [← h2]; exact h1
    · simp only [hr, if_false] at h1 h2
      rw [h2]; exact VS.sub_sound h1 h3
  refine ⟨?_, cand, ?_, ?_⟩
  · intro a' ha'
    rw [hprgt]
    exact hc a' ha'
  · rw [hregs]; exact hcm
  · have hcand := hb.frame
    exact {
      pc := by rw [hregs]; exact hcpc.symm
      sp := by rw [hregs]; exact hcs.symm
      a := by rw [hregs]; exact hreg hca ga hb.a
      x := by rw [hregs]; exact hreg hcx gx hb.x
      y := by rw [hregs]; exact hreg hcy gy hb.y
      p := by rw [hregs]; exact hcp
      i := by rw [hregs]; simpa using hI'
      bad := by rw [hbadt]; exact hb.bad
      cells := by
        intro c hcin
        rw [hramt]
        have hcc' := hcc c hcin
        rw [gop] at hcc'
        refine cellCoveredR_sound hb (k := k) (a := operandAddr k b1 b2 ⟨pc, a, x, y, sp, p⟩ _ _)
          (v := if usesV k then vOf ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ k else 0) ?_ hcc'
        intro huv
        simp only [huv, if_true, vOf, loOf, hiOf, mr, b1Of, b2Of] at hb1 hb2 ⊢
        rw [hb1, hb2]
      glob := by
        intro i hia
        rw [hramt, applyW_lookup]
        cases hl : wrLookup (eval k b1 b2 ⟨pc, a, x, y, sp, p⟩ _ _ _).wr i with
        | some v =>
          rcases (wrLookup_ok (List.all_eq_true.mpr hw) hl).2 with h1 | h1
          · exact h1
          · rw [hia] at h1; cases h1
        | none => exact hb.glob i
      frame := by
        intro i hpi
        rw [hramt, applyW_lookup]
        cases hl : wrLookup (eval k b1 b2 ⟨pc, a, x, y, sp, p⟩ _ _ _).wr i with
        | some v =>
          have := (wrLookup_ok (List.all_eq_true.mpr hw) hl).1
          rw [hpi] at this
          cases this
        | none => exact hb.frame i hpi }

/-- One instruction: a checked table keeps the invariant, the bounds and the protected RAM. -/
theorem inv_step {rom : UInt16 → UInt8} {exit prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    {s : Plain} (hchk : check rom exit prot g T = true) (hc : Code rom s) (h : Inv prot g ram0 T s)
    (hx : exit s.regs.pc = false) (ha : AssumedOk g (CPU.step.run s).2.ram) :
    Code rom (CPU.step.run s).2 ∧ Inv prot g ram0 T (CPU.step.run s).2 := by
  obtain ⟨b, hbm, hb⟩ := h
  have hbox := by
    simp only [check, List.all_eq_true, List.mem_range] at hchk
    exact hchk _ (table_at_lt s.regs.pc) b hbm
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq] at hbox
  obtain ⟨_, hstep⟩ := hbox
  rw [← hb.pc] at hstep
  rcases hstep with h1 | h1
  · rw [hx] at h1; simp at h1
  · obtain ⟨h2, c, h3, h4⟩ := inv_step_box h1 hc hb
    exact ⟨h2, c, h3, h4.holds ha⟩

/-- A checked table's invariant holds along any bounded run to the table's one exit. The run stops there or runs out of
fuel; this does not assert the exit is reached. -/
theorem inv_runTo {rom : UInt16 → UInt8} {exit prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    (hchk : check rom exit prot g T = true) (htop : gAt g 0x300 = .top) (htop2 : gAt g 0x340 = .top) (stop : UInt16) (hexit : ∀ a, exit a = true → a = stop)
    (n : Nat) (s : Plain) (hc : Code rom s) (h : Inv prot g ram0 T s) :
    let t := ((CPU.runTo (σ := Plain) stop n).run s).2
    Code rom t ∧ Inv prot g ram0 T t := by
  induction n generalizing s with
  | zero => exact ⟨hc, h⟩
  | succ n ih =>
    have hregs : Bus.regs s = s.regs := rfl
    by_cases hx : s.regs.pc = stop
    · simpa only [CPU.runTo, CPU.getRegs, hregs, hx, ↓reduceIte, bind, StateT.bind,
        pure, StateT.pure, StateT.run] using And.intro hc h
    · have hx' : exit s.regs.pc = false := by
        cases he : exit s.regs.pc with
        | false => rfl
        | true => exact absurd (hexit _ he) hx
      have hs := inv_step hchk hc h hx' (assumedOk_of_top htop htop2 _)
      have hn := ih (CPU.step.run s).2 hs.1 hs.2
      simp only [CPU.runTo, CPU.getRegs, hregs, hx, ↓reduceIte, bind, StateT.bind, StateT.run]
      cases he : CPU.step s with
      | mk u t => simpa only [StateT.run, he] using hn

/-- A state an entry box allows is in the invariant, if the table has a box containing the entry box. -/
theorem inv_of_entry {prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8} {e : Box} {s : Plain}
    (hin : entryIn g T e = true) (h : Holds prot g ram0 e s) : Inv prot g ram0 T s := by
  simp only [entryIn, List.any_eq_true] at hin
  obtain ⟨c, hc, hle⟩ := hin
  simp only [Box.le, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hle
  obtain ⟨⟨⟨⟨⟨⟨hpc, hs⟩, ha⟩, hx⟩, hy⟩, hp⟩, hcells⟩ := hle
  refine ⟨c, ?_, ?_⟩
  · rw [h.pc]; exact hc
  · exact {
      pc := by rw [h.pc, hpc]
      sp := by rw [h.sp, hs]
      a := VS.sub_sound ha h.a
      x := VS.sub_sound hx h.x
      y := VS.sub_sound hy h.y
      p := VS.sub_sound hp h.p
      i := h.i
      bad := h.bad
      cells := fun d hd => by simpa [applyW] using cellCovered_sound h (hcells d hd)
      glob := h.glob
      frame := h.frame }

end Smb.Abs
