import Smb.StepLemmas
import Smb.Game
import Smb.Run
import Std.Tactic.BVDecide

/-!
# A five-opcode value-set certificate for the timer loop

The abstract interpreter is untrusted. A table of boxes is checked by `check`, whose soundness is proved
from the machine's semantics. Here the table is the per-`X` partition of `DecTimersLoop` (`$810E`-`$8118`),
the loop that decrements the game's timers each frame:

    810E  BD 80 07  lda Timers,x
    8111  F0 03     beq SkipExpTimer
    8113  DE 80 07  dec Timers,x
    8116  CA        dex
    8117  10 F5     bpl DecTimersLoop

The domain contains: exact partition value of `X`, a set per tracked RAM byte, and the relation
"Z reflects this RAM byte", which is what lets `beq` refine the byte so that `dec` cannot wrap. Only these five
opcodes are covered, at instruction PCs from $8000 through $FFF0. `absStep` returns `none`
for other instructions or unsupported addressing conditions; the checker rejects them.

The timer bound is an entry assumption that this certificate preserves. The checked table
is not a proof that game execution reaches that entry or initially satisfies the bound.
`inv_runTo` carries code and the invariant through bounded Plain runs, stopping at the
specified exit; it does not prove termination, a full NES simulation, or a whole-game bound.
-/
namespace Smb.ValueSets
open CPU

-- No enum translation is needed here. Disabling it avoids exporting an unused
-- PUnit.enumToBitVec helper that collides with independently built proof modules.

/-! ### Reading one instruction on the plain machine -/

theorem step_eq (s : Plain) :
    (CPU.step.run s).2 =
      ((CPU.stepTail (Plain.memRead s.ram s.prg s.regs.pc)).run
        ⟨⟨s.regs.pc + 1, s.regs.a, s.regs.x, s.regs.y, s.regs.s, s.regs.p⟩, s.ram, s.prg, s.cyc + 1,
          s.bad || !Plain.readable s.regs.pc⟩).2 := rfl

theorem memRead_rom (ram prg : UInt16 → UInt8) (a : UInt16) (h : 0x8000 ≤ a) :
    Plain.memRead ram prg a = prg (a &&& 0x7FFF) := by
  have : Plain.inRam a = false := by
    simp only [Plain.inRam, decide_eq_false_iff_not]; bv_decide (config := { enums := false })
  simp [Plain.memRead, this]

theorem readable_rom (a : UInt16) (h : 0x8000 ≤ a) : Plain.readable a = true := by
  simp [Plain.readable, h]

private theorem lt8192_false (b : UInt16) (h : 0x8000 ≤ b) : decide (b < 8192) = false := by
  simp only [decide_eq_false_iff_not]; bv_decide (config := { enums := false })

private theorem ge32768_true (b : UInt16) (h : 0x8000 ≤ b) : decide (32768 ≤ b) = true := by
  simp only [decide_eq_true_eq]; exact h

/-- The little-endian operand of an absolute instruction. -/
def base (lo hi : UInt8) : UInt16 := lo.toUInt16 ||| hi.toUInt16 <<< 8

/-- Target of a relative branch whose operand byte is `off`, for the branch instruction at `pc`. -/
def relTarget (pc : UInt16) (off : UInt8) : UInt16 :=
  pc + 2 + off.toUInt16 + (bif off &&& 128 != 0 then 65280 else 0)

/-- `DEX`. -/
theorem step_dex (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 0xCA) (hi : s.regs.p &&& 4 ≠ 0) :
    let t := (CPU.step.run s).2
    t.regs.pc = s.regs.pc + 1 ∧ t.regs.x = s.regs.x - 1 ∧ t.prg = s.prg ∧ t.bad = s.bad ∧
      t.regs.p &&& 4 ≠ 0 ∧ t.ram = s.ram ∧ (t.regs.p &&& 128 ≠ 0 ↔ t.regs.x ≥ 0x80) := by
  obtain ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ := s
  simp only at h0 h2 hop hi
  have h1 : (0x8000 : UInt16) ≤ pc + 1 := by bv_decide (config := { enums := false })
  simp only [step_eq, memRead_rom ram prg pc h0, hop, readable_rom pc h0, Bool.not_true, Bool.or_false]
  rw [show (0xCA : UInt8) = 202 from rfl, StepLemma.tail_ca]
  simp only [lt8192_false _ h1, ge32768_true _ h1]
  and_intros
  all_goals first | trivial | rfl | (simp only []; bv_decide (config := { enums := false })) | bv_decide (config := { enums := false })

/-- `LDA abs,X`, the access in RAM. -/
theorem step_lda_abx (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 0xBD) (hi : s.regs.p &&& 4 ≠ 0)
    (lo hi' : UInt8) (hlo : s.prg (s.regs.pc + 1 &&& 0x7FFF) = lo) (hhi : s.prg (s.regs.pc + 2 &&& 0x7FFF) = hi')
    (hb : base lo hi' ≤ 0x1F00) :
    let t := (CPU.step.run s).2
    t.regs.pc = s.regs.pc + 3 ∧ t.regs.x = s.regs.x ∧ t.prg = s.prg ∧ t.bad = s.bad ∧
      t.regs.p &&& 4 ≠ 0 ∧ t.ram = s.ram ∧
      (t.regs.p &&& 2 ≠ 0 ↔ s.ram (base lo hi' + s.regs.x.toUInt16 &&& 0x7FF) = 0) := by
  obtain ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ := s
  simp only at h0 h2 hop hi hlo hhi
  have h1 : (0x8000 : UInt16) ≤ pc + 1 := by bv_decide (config := { enums := false })
  have h3 : (0x8000 : UInt16) ≤ pc + 1 + 1 := by bv_decide (config := { enums := false })
  have hhi2 : prg (pc + 1 + 1 &&& 32767) = hi' := by
    rw [← hhi]; congr 1; bv_decide (config := { enums := false })
  simp only [step_eq, memRead_rom ram prg pc h0, hop, readable_rom pc h0, Bool.not_true, Bool.or_false]
  rw [show (0xBD : UInt8) = 189 from rfl, StepLemma.tail_bd]
  simp only [lt8192_false _ h1, lt8192_false _ h3, ge32768_true _ h1, ge32768_true _ h3, hlo, hhi2, Bool.false_or, Bool.not_true,
    Bool.or_false, Bool.cond_false]
  generalize hB : (lo.toUInt16 ||| hi'.toUInt16 <<< 8) = B
  have hb' : B ≤ 0x1F00 := by rw [← hB]; exact hb
  clear hb
  have hea : decide (B + x.toUInt16 < 8192) = true := by
    simp only [decide_eq_true_eq]; bv_decide (config := { enums := false })
  simp only [hea, Bool.cond_true]
  have hbase : base lo hi' = B := hB
  rw [hbase]
  generalize ram (B + x.toUInt16 &&& 2047) = v
  and_intros
  all_goals first | trivial | rfl | (simp only []; bv_decide (config := { enums := false })) | bv_decide (config := { enums := false })

/-- `DEC abs,X`, the access in RAM. -/
theorem step_dec_abx (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 0xDE) (hi : s.regs.p &&& 4 ≠ 0)
    (lo hi' : UInt8) (hlo : s.prg (s.regs.pc + 1 &&& 0x7FFF) = lo) (hhi : s.prg (s.regs.pc + 2 &&& 0x7FFF) = hi')
    (hb : base lo hi' ≤ 0x1F00) :
    let t := (CPU.step.run s).2
    let ea := base lo hi' + s.regs.x.toUInt16 &&& 0x7FF
    t.regs.pc = s.regs.pc + 3 ∧ t.regs.x = s.regs.x ∧ t.prg = s.prg ∧ t.bad = s.bad ∧
      t.regs.p &&& 4 ≠ 0 ∧ (∀ i, t.ram i = if i = ea then s.ram ea - 1 else s.ram i) := by
  obtain ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ := s
  simp only at h0 h2 hop hi hlo hhi
  have h1 : (0x8000 : UInt16) ≤ pc + 1 := by bv_decide (config := { enums := false })
  have h3 : (0x8000 : UInt16) ≤ pc + 1 + 1 := by bv_decide (config := { enums := false })
  have hhi2 : prg (pc + 1 + 1 &&& 32767) = hi' := by
    rw [← hhi]; congr 1; bv_decide (config := { enums := false })
  simp only [step_eq, memRead_rom ram prg pc h0, hop, readable_rom pc h0, Bool.not_true, Bool.or_false]
  rw [show (0xDE : UInt8) = 222 from rfl, StepLemma.tail_de]
  simp only [lt8192_false _ h1, lt8192_false _ h3, ge32768_true _ h1, ge32768_true _ h3, hlo, hhi2, Bool.false_or, Bool.not_true,
    Bool.or_false, Bool.cond_false]
  generalize hB : (lo.toUInt16 ||| hi'.toUInt16 <<< 8) = B
  have hb' : B ≤ 0x1F00 := by rw [← hB]; exact hb
  clear hb
  have hea : decide (B + x.toUInt16 < 8192) = true := by
    simp only [decide_eq_true_eq]; bv_decide (config := { enums := false })
  have hea2 : decide (B &&& 65280 ||| B + x.toUInt16 &&& 255 < 8192) = true := by
    simp only [decide_eq_true_eq]; bv_decide (config := { enums := false })
  simp only [hea, Bool.cond_true, Bool.true_and]
  have hbase : base lo hi' = B := hB
  rw [hbase]
  have hr : ∀ i, (bif i == B + x.toUInt16 &&& 2047 then
        ram (B + x.toUInt16 &&& 2047) + 255
      else
        bif i == B + x.toUInt16 &&& 2047 then ram (B + x.toUInt16 &&& 2047) else ram i) =
      if i = B + x.toUInt16 &&& 2047 then ram (B + x.toUInt16 &&& 2047) - 1 else ram i := by
    intro i
    by_cases h : i = B + x.toUInt16 &&& 2047
    · rw [h]
      simp only [beq_self_eq_true, Bool.cond_true, ite_true]
      generalize ram (B + x.toUInt16 &&& 2047) = v
      bv_decide (config := { enums := false })
    · have : (i == B + x.toUInt16 &&& 2047) = false := by simpa using h
      simp [this, h]
  have hp : (p &&& 4 == 0) = false := by simpa using hi
  refine ⟨by bv_decide (config := { enums := false }), trivial, trivial, ?_, ?_, hr⟩
  · simp [hea2, hp]
  · generalize ram (B + x.toUInt16 &&& 2047) = v
    bv_decide (config := { enums := false })

/-- `BEQ`, either way. -/
theorem step_beq (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 0xF0) (hi : s.regs.p &&& 4 ≠ 0)
    (off : UInt8) (hoff : s.prg (s.regs.pc + 1 &&& 0x7FFF) = off) (ht : 0x8000 ≤ relTarget s.regs.pc off) :
    let t := (CPU.step.run s).2
    (s.regs.p &&& 2 ≠ 0 → t.regs.pc = relTarget s.regs.pc off) ∧
      (s.regs.p &&& 2 = 0 → t.regs.pc = s.regs.pc + 2) ∧
      t.regs.x = s.regs.x ∧ t.regs.p = s.regs.p ∧ t.prg = s.prg ∧ t.bad = s.bad ∧ t.ram = s.ram := by
  obtain ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ := s
  simp only at h0 h2 hop hi hoff ht
  have h1 : (0x8000 : UInt16) ≤ pc + 1 := by bv_decide (config := { enums := false })
  have h3 : (0x8000 : UInt16) ≤ pc + 1 + 1 := by bv_decide (config := { enums := false })
  simp only [step_eq, memRead_rom ram prg pc h0, hop, readable_rom pc h0, Bool.not_true, Bool.or_false]
  rw [show (0xF0 : UInt8) = 240 from rfl, StepLemma.tail_f0]
  have hp : (p &&& 4 == 0) = false := by simpa using hi
  have hT : relTarget pc off = pc + 1 + 1 + off.toUInt16 + (bif off &&& 128 != 0 then 65280 else 0) := by
    simp only [relTarget]; congr 2; bv_decide (config := { enums := false })
  have hA : ∀ T : UInt16, decide (pc + 1 + 1 &&& 65280 ||| T &&& 255 < 8192) = false := by
    intro T; simp only [decide_eq_false_iff_not]; bv_decide (config := { enums := false })
  have hB : ∀ T : UInt16, decide (32768 ≤ pc + 1 + 1 &&& 65280 ||| T &&& 255) = true := by
    intro T; simp only [decide_eq_true_eq]; bv_decide (config := { enums := false })
  have h22 : pc + 1 + 1 = pc + 2 := by bv_decide (config := { enums := false })
  simp only [lt8192_false _ h1, lt8192_false _ h3, ge32768_true _ h1, ge32768_true _ h3, hoff, Bool.cond_false, hp, hA, hB]
  rw [hT]
  generalize pc + 1 + 1 + off.toUInt16 + (bif off &&& 128 != 0 then 65280 else 0) = T
  generalize hq : ((T ^^^ pc + 1 + 1) &&& 65280 != 0) = q
  by_cases hc : p &&& 2 = 0
  · have hc' : (p &&& 2 != 0) = false := by simpa using hc
    cases q <;> simp [hc, h22]
  · have hc' : (p &&& 2 != 0) = true := by simpa using hc
    cases q <;> simp [hc, hc', h22]

/-- `BPL`, either way. -/
theorem step_bpl (s : Plain) (h0 : 0x8000 ≤ s.regs.pc) (h2 : s.regs.pc ≤ 0xFFF0)
    (hop : s.prg (s.regs.pc &&& 0x7FFF) = 0x10) (hi : s.regs.p &&& 4 ≠ 0)
    (off : UInt8) (hoff : s.prg (s.regs.pc + 1 &&& 0x7FFF) = off) (ht : 0x8000 ≤ relTarget s.regs.pc off) :
    let t := (CPU.step.run s).2
    (s.regs.p &&& 128 = 0 → t.regs.pc = relTarget s.regs.pc off) ∧
      (s.regs.p &&& 128 ≠ 0 → t.regs.pc = s.regs.pc + 2) ∧
      t.regs.x = s.regs.x ∧ t.regs.p = s.regs.p ∧ t.prg = s.prg ∧ t.bad = s.bad ∧ t.ram = s.ram := by
  obtain ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ := s
  simp only at h0 h2 hop hi hoff ht
  have h1 : (0x8000 : UInt16) ≤ pc + 1 := by bv_decide (config := { enums := false })
  have h3 : (0x8000 : UInt16) ≤ pc + 1 + 1 := by bv_decide (config := { enums := false })
  simp only [step_eq, memRead_rom ram prg pc h0, hop, readable_rom pc h0, Bool.not_true, Bool.or_false]
  rw [show (0x10 : UInt8) = 16 from rfl, StepLemma.tail_10]
  have hp : (p &&& 4 == 0) = false := by simpa using hi
  have hT : relTarget pc off = pc + 1 + 1 + off.toUInt16 + (bif off &&& 128 != 0 then 65280 else 0) := by
    simp only [relTarget]; congr 2; bv_decide (config := { enums := false })
  have hA : ∀ T : UInt16, decide (pc + 1 + 1 &&& 65280 ||| T &&& 255 < 8192) = false := by
    intro T; simp only [decide_eq_false_iff_not]; bv_decide (config := { enums := false })
  have hB : ∀ T : UInt16, decide (32768 ≤ pc + 1 + 1 &&& 65280 ||| T &&& 255) = true := by
    intro T; simp only [decide_eq_true_eq]; bv_decide (config := { enums := false })
  have h22 : pc + 1 + 1 = pc + 2 := by bv_decide (config := { enums := false })
  simp only [lt8192_false _ h1, lt8192_false _ h3, ge32768_true _ h1, ge32768_true _ h3, hoff, Bool.cond_false, hp, hA, hB]
  rw [hT]
  generalize pc + 1 + 1 + off.toUInt16 + (bif off &&& 128 != 0 then 65280 else 0) = T
  generalize hq : ((T ^^^ pc + 1 + 1) &&& 65280 != 0) = q
  by_cases hc : p &&& 128 = 0
  · have hc' : (p &&& 128 != 0) = false := by simpa using hc
    cases q <;> simp [hc, h22]
  · have hc' : (p &&& 128 != 0) = true := by simpa using hc
    cases q <;> simp [hc, hc', h22]

/-! ### The checker -/

abbrev VS := UInt8 → Bool

/-- Exhaustive inclusion check over all 256 bytes; value sets are Boolean functions. -/
def all256 (f : UInt8 → Bool) : Bool := (List.range 256).all fun n => f n.toUInt8

theorem all256_spec {f : UInt8 → Bool} (h : all256 f = true) (v : UInt8) : f v = true := by
  have hv := v.toNat_lt
  have := List.all_eq_true.mp h v.toNat (List.mem_range.mpr hv)
  have hv2 : v.toNat.toUInt8 = v := by simp
  rw [hv2] at this
  exact this

/-- An abstract state: exact PC, exact partition value of `X`, the flag relations, and a set per tracked byte.
Untracked bytes are unconstrained. -/
structure Box where
  pc : UInt16
  x : UInt8
  zOf : Option UInt16
  nOfX : Bool
  cells : List (UInt16 × VS)

structure Holds (b : Box) (s : Plain) : Prop where
  pc : s.regs.pc = b.pc
  x : s.regs.x = b.x
  i : s.regs.p &&& 4 ≠ 0
  bad : s.bad = false
  z : ∀ i, b.zOf = some i → (s.regs.p &&& 2 ≠ 0 ↔ s.ram i = 0)
  n : b.nOfX = true → (s.regs.p &&& 128 ≠ 0 ↔ s.regs.x ≥ 0x80)
  cells : ∀ c ∈ b.cells, c.2 (s.ram c.1) = true

/-- The ROM holds the code: stated for addresses the machine fetches from. -/
def Code (rom : UInt16 → UInt8) (s : Plain) : Prop := ∀ a, 0x8000 ≤ a → s.prg (a &&& 0x7FFF) = rom a

def refineCells (i : UInt16) (p : UInt8 → Bool) (cs : List (UInt16 × VS)) : List (UInt16 × VS) :=
  cs.map fun c => if c.1 == i then (c.1, fun v => c.2 v && p v) else c

def decCells (i : UInt16) (cs : List (UInt16 × VS)) : List (UInt16 × VS) :=
  cs.map fun c => if c.1 == i then (c.1, fun v => c.2 (v + 1)) else c

/-- One abstract step, from the ROM's bytes. `none`: the checker does not cover this instruction. -/
def absStep (rom : UInt16 → UInt8) (b : Box) : Option (List Box) :=
  if !(decide (0x8000 ≤ b.pc) && decide (b.pc ≤ 0xFFF0)) then none else
  let op := rom b.pc
  let lo := rom (b.pc + 1)
  let hi := rom (b.pc + 2)
  let ea := base lo hi + b.x.toUInt16 &&& 0x7FF
  if op = 0xBD then
    if base lo hi ≤ 0x1F00 then some [{ b with pc := b.pc + 3, zOf := some ea, nOfX := false }] else none
  else if op = 0xDE then
    if base lo hi ≤ 0x1F00 then
      some [{ b with pc := b.pc + 3, zOf := none, nOfX := false, cells := decCells ea b.cells }]
    else none
  else if op = 0xCA then
    some [{ b with pc := b.pc + 1, x := b.x - 1, zOf := none, nOfX := true }]
  else if op = 0xF0 then
    if 0x8000 ≤ relTarget b.pc lo then
      match b.zOf with
      | none => none
      | some i =>
        some [{ b with pc := relTarget b.pc lo, cells := refineCells i (· == 0) b.cells },
              { b with pc := b.pc + 2, cells := refineCells i (· != 0) b.cells }]
    else none
  else if op = 0x10 then
    if 0x8000 ≤ relTarget b.pc lo ∧ b.nOfX = true then
      if b.x ≥ 0x80 then some [{ b with pc := b.pc + 2 }] else some [{ b with pc := relTarget b.pc lo }]
    else none
  else none

theorem absStep_sound {rom : UInt16 → UInt8} {b : Box} {s : Plain} {l : List Box}
    (hc : Code rom s) (hb : Holds b s) (hl : absStep rom b = some l) :
    (CPU.step.run s).2.prg = s.prg ∧ ∃ b' ∈ l, Holds b' (CPU.step.run s).2 := by
  have hpc := hb.pc
  simp only [absStep] at hl
  split at hl
  · cases hl
  rename_i hg
  have hg' : 0x8000 ≤ b.pc ∧ b.pc ≤ 0xFFF0 := by
    simpa using hg
  have h0 : 0x8000 ≤ s.regs.pc := hpc ▸ hg'.1
  have h2 : s.regs.pc ≤ 0xFFF0 := hpc ▸ hg'.2
  have hop : s.prg (s.regs.pc &&& 0x7FFF) = rom b.pc := by rw [hc _ h0, hpc]
  have hlo : s.prg (s.regs.pc + 1 &&& 0x7FFF) = rom (b.pc + 1) := by
    rw [hc _ (by bv_decide (config := { enums := false })), hpc]
  have hhi : s.prg (s.regs.pc + 2 &&& 0x7FFF) = rom (b.pc + 2) := by
    rw [hc _ (by bv_decide (config := { enums := false })), hpc]
  have hrom : s.regs.x = b.x := hb.x
  split at hl
  · -- LDA abs,X
    rename_i hopv
    split at hl
    · rename_i hbase
      cases hl
      have := step_lda_abx s h0 h2 (hop.trans hopv) hb.i _ _ hlo hhi hbase
      obtain ⟨p1, p2, pprg, p4, p5, p6, p7⟩ := this
      refine ⟨pprg, ?_⟩
      refine ⟨_, List.mem_singleton.mpr rfl, ⟨?_, ?_, p5, ?_, ?_, ?_, ?_⟩⟩
      · simp only [p1, hpc]
      · simp only [p2, hrom]
      · rw [p4]; exact hb.bad
      · intro i hi
        simp only [Option.some.injEq] at hi
        subst hi
        rw [p6, ← hrom]; exact p7
      · intro h; simp at h
      · intro c hcm
        rw [p6]; exact hb.cells c hcm
    · cases hl
  · split at hl
    · -- DEC abs,X
      rename_i hopv
      split at hl
      · rename_i hbase
        cases hl
        have := step_dec_abx s h0 h2 (hop.trans hopv) hb.i _ _ hlo hhi hbase
        obtain ⟨p1, p2, pprg, p4, p5, p6⟩ := this
        refine ⟨pprg, ?_⟩
        refine ⟨_, List.mem_singleton.mpr rfl, ⟨?_, ?_, p5, ?_, ?_, ?_, ?_⟩⟩
        · simp only [p1, hpc]
        · simp only [p2, hrom]
        · rw [p4]; exact hb.bad
        · intro i hi; simp at hi
        · intro h; simp at h
        · intro c hcm
          simp only [decCells, List.mem_map] at hcm
          obtain ⟨c0, hc0, rfl⟩ := hcm
          have hold := hb.cells c0 hc0
          rw [hrom] at p6
          by_cases he : c0.1 = base (rom (b.pc + 1)) (rom (b.pc + 2)) + b.x.toUInt16 &&& 0x7FF
          · have hbeq : (c0.1 == base (rom (b.pc + 1)) (rom (b.pc + 2)) + b.x.toUInt16 &&& 0x7FF) = true := by
              simpa using he
            simp only [ite_true, p6, ← he, beq_self_eq_true]
            have e : s.ram c0.1 - 1 + 1 = s.ram c0.1 := by
              generalize s.ram c0.1 = v; bv_decide (config := { enums := false })
            rw [e]; exact hold
          · have hne : (c0.1 == base (rom (b.pc + 1)) (rom (b.pc + 2)) + b.x.toUInt16 &&& 0x7FF) = false := by
              simpa using he
            simp only [hne, Bool.false_eq_true, ite_false, p6, he]
            exact hold
      · cases hl
    · split at hl
      · -- DEX
        rename_i hopv
        cases hl
        have := step_dex s h0 h2 (hop.trans hopv) hb.i
        obtain ⟨p1, p2, pprg, p4, p5, p6, p7⟩ := this
        refine ⟨pprg, ?_⟩
        refine ⟨_, List.mem_singleton.mpr rfl, ⟨?_, ?_, p5, ?_, ?_, ?_, ?_⟩⟩
        · simp only [p1, hpc]
        · simp only [p2, hrom]
        · rw [p4]; exact hb.bad
        · intro i hi; simp at hi
        · intro _; exact p7
        · intro c hcm; rw [p6]; exact hb.cells c hcm
      · split at hl
        · -- BEQ
          rename_i hopv
          split at hl
          · rename_i htgt
            have ht' : 0x8000 ≤ relTarget s.regs.pc (rom (b.pc + 1)) := by rw [hpc]; exact htgt
            have := step_beq s h0 h2 (hop.trans hopv) hb.i _ hlo ht'
            obtain ⟨pt, pf, p2, p3, pprg, p5, p6⟩ := this
            refine ⟨pprg, ?_⟩
            cases hz : b.zOf with
            | none => simp [hz] at hl
            | some i =>
              simp only [hz, Option.some.injEq] at hl
              subst hl
              have hzi := hb.z i hz
              by_cases hf : s.regs.p &&& 2 = 0
              · -- not taken
                refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
                · simp only [pf hf, hpc]
                · simp only [p2, hrom]
                · rw [p3]; exact hb.i
                · rw [p5]; exact hb.bad
                · intro j hj; rw [p3, p6]; simp only at hj; rw [← hz] at hj; exact hb.z j hj
                · intro hj; rw [p3, p2]; exact hb.n hj
                · intro c hcm
                  simp only [refineCells, List.mem_map] at hcm
                  obtain ⟨c0, hc0, rfl⟩ := hcm
                  rw [p6]
                  have hold := hb.cells c0 hc0
                  by_cases he : c0.1 = i
                  · have hne : s.ram i ≠ 0 := fun h => (hzi.mpr h) hf
                    simp [he, hne]
                    rw [he] at hold; exact hold
                  · simp [he, hold]
              · -- taken
                refine ⟨_, List.mem_cons_self, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
                · simp only [pt hf, hpc]
                · simp only [p2, hrom]
                · rw [p3]; exact hb.i
                · rw [p5]; exact hb.bad
                · intro j hj; rw [p3, p6]; simp only at hj; rw [← hz] at hj; exact hb.z j hj
                · intro hj; rw [p3, p2]; exact hb.n hj
                · intro c hcm
                  simp only [refineCells, List.mem_map] at hcm
                  obtain ⟨c0, hc0, rfl⟩ := hcm
                  rw [p6]
                  have hold := hb.cells c0 hc0
                  by_cases he : c0.1 = i
                  · have h00 : s.ram i = 0 := hzi.mp hf
                    simp [he, h00]
                    rw [he, h00] at hold; exact hold
                  · simp [he, hold]
          · cases hl
        · split at hl
          · -- BPL
            rename_i hopv
            split at hl
            · rename_i hgu
              obtain ⟨htgt, hnx⟩ := hgu
              have ht' : 0x8000 ≤ relTarget s.regs.pc (rom (b.pc + 1)) := by rw [hpc]; exact htgt
              have := step_bpl s h0 h2 (hop.trans hopv) hb.i _ hlo ht'
              obtain ⟨pt, pf, p2, p3, pprg, p5, p6⟩ := this
              refine ⟨pprg, ?_⟩
              have hni := hb.n hnx
              split at hl
              · -- X negative: falls through
                rename_i hneg
                cases hl
                have hnf : s.regs.p &&& 128 ≠ 0 := hni.mpr (by rw [hrom]; exact hneg)
                refine ⟨_, List.mem_singleton.mpr rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
                · simp only [pf hnf, hpc]
                · simp only [p2, hrom]
                · rw [p3]; exact hb.i
                · rw [p5]; exact hb.bad
                · intro j hj; rw [p3, p6]; simp only at hj; exact hb.z j hj
                · intro hj; rw [p3, p2]; exact hb.n hj
                · intro c hcm; rw [p6]; exact hb.cells c hcm
              · rename_i hneg
                cases hl
                have hnf : s.regs.p &&& 128 = 0 := by
                  apply Classical.byContradiction
                  intro hne
                  exact hneg (by rw [← hrom]; exact hni.mp hne)
                refine ⟨_, List.mem_singleton.mpr rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
                · simp only [pt hnf, hpc]
                · simp only [p2, hrom]
                · rw [p3]; exact hb.i
                · rw [p5]; exact hb.bad
                · intro j hj; rw [p3, p6]; simp only at hj; exact hb.z j hj
                · intro hj; rw [p3, p2]; exact hb.n hj
                · intro c hcm; rw [p6]; exact hb.cells c hcm
            · cases hl
          · cases hl

/-- Every byte `t` constrains, `b` constrains at least as tightly, and likewise for the flags. -/
def leBox (b t : Box) : Bool :=
  b.pc == t.pc && b.x == t.x &&
  (match t.zOf with | none => true | some i => b.zOf == some i) &&
  (!t.nOfX || b.nOfX) &&
  t.cells.all fun c => b.cells.any fun c' => c'.1 == c.1 && all256 fun v => !c'.2 v || c.2 v

theorem leBox_sound {b t : Box} {s : Plain} (h : leBox b t = true) (hb : Holds b s) : Holds t s := by
  simp only [leBox, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨hp, hx⟩, hz⟩, hn⟩, hc⟩ := h
  refine ⟨hb.pc.trans hp, hb.x.trans hx, hb.i, hb.bad, ?_, ?_, ?_⟩
  · intro i hi
    rw [hi] at hz
    exact hb.z i (by simpa using hz)
  · intro htn
    apply hb.n
    simpa [htn] using hn
  · intro c hcm
    obtain ⟨c', hc'm, heq, hall⟩ := hc c hcm
    have h1 := hb.cells c' hc'm
    have h2 := all256_spec hall (s.ram c.1)
    rw [← heq] at h2 ⊢
    rw [h1] at h2
    simpa using h2

/-- The check: every box's every successor is covered by some box in the table. Boxes at `exit` are not stepped. -/
def check (rom : UInt16 → UInt8) (T : List Box) (exit : UInt16) : Bool :=
  T.all fun b => b.pc == exit ||
    match absStep rom b with
    | none => false
    | some l => l.all fun b' => T.any (leBox b')

def Inv (T : List Box) (s : Plain) : Prop := ∃ b ∈ T, Holds b s

/-- One checked Plain step preserves both the ROM interpretation and table membership.
The exit is deliberately exempt from successor checking. -/
theorem inv_step {rom : UInt16 → UInt8} {T : List Box} {exit : UInt16} (hchk : check rom T exit = true)
    {s : Plain} (hc : Code rom s) (h : Inv T s) (hx : s.regs.pc ≠ exit) :
    Code rom (CPU.step.run s).2 ∧ Inv T (CPU.step.run s).2 := by
  obtain ⟨b, hbT, hb⟩ := h
  have hb1 := List.all_eq_true.mp hchk b hbT
  have hne : (b.pc == exit) = false := by
    have := hb.pc; simp only [beq_eq_false_iff_ne]; rw [← this]; exact hx
  simp only [hne, Bool.false_or] at hb1
  cases hab : absStep rom b with
  | none => simp [hab] at hb1
  | some l =>
    simp only [hab, List.all_eq_true, List.any_eq_true] at hb1
    obtain ⟨hprg, b', hb'l, hb'⟩ := absStep_sound hc hb hab
    obtain ⟨t, htT, hle⟩ := hb1 b' hb'l
    refine ⟨?_, t, htT, leBox_sound hle hb'⟩
    intro a ha
    rw [hprg]
    exact hc a ha

/-- Every bounded execution prefix stays in the checked invariant. The run stops
at exit or at fuel exhaustion; this theorem does not assert that exit is reached. -/
theorem inv_runTo {rom : UInt16 → UInt8} {T : List Box} {exit : UInt16}
    (hchk : check rom T exit = true) (fuel : Nat) (s : Plain)
    (hc : Code rom s) (h : Inv T s) :
    let t := ((CPU.runTo (σ := Plain) exit fuel).run s).2
    Code rom t ∧ Inv T t := by
  induction fuel generalizing s with
  | zero => exact ⟨hc, h⟩
  | succ fuel ih =>
    have hregs : Bus.regs s = s.regs := rfl
    by_cases hx : s.regs.pc = exit
    · simpa only [CPU.runTo, CPU.getRegs, hregs, hx, ↓reduceIte, bind, StateT.bind,
        pure, StateT.pure, StateT.run] using And.intro hc h
    · have hs := inv_step hchk hc h hx
      have hn := ih (CPU.step.run s).2 hs.1 hs.2
      simp only [CPU.runTo, CPU.getRegs, hregs, hx, ↓reduceIte, bind, StateT.bind, StateT.run]
      cases he : CPU.step s with
      | mk u t => simpa only [StateT.run, he] using hn

/-! ### The instance: `DecTimersLoop`, per-`X` partition, every timer at most `$7F` -/

/-- The real ROM, as the machine reads it. -/
def decTimersRom (a : UInt16) : UInt8 := prg.get! (a &&& 0x7FFF).toNat

def timerIdx (n : Nat) : UInt16 := 0x780 + n.toUInt16

/-- Each of the 36 timers at most `$7F`; `tight` also says the current timer is non-zero. -/
def timerCells (tight : Option Nat) : List (UInt16 × VS) :=
  (List.range 36).map fun n =>
    (timerIdx n, fun v => decide (v ≤ 0x7F) && (tight != some n || v != 0))

def table : List Box :=
  (List.range 36).flatMap (fun n =>
    let x := n.toUInt8
    [ { pc := 0x810E, x, zOf := none, nOfX := false, cells := timerCells none },
      { pc := 0x8111, x, zOf := some (timerIdx n), nOfX := false, cells := timerCells none },
      { pc := 0x8113, x, zOf := none, nOfX := false, cells := timerCells (some n) },
      { pc := 0x8116, x, zOf := none, nOfX := false, cells := timerCells none },
      { pc := 0x8117, x, zOf := none, nOfX := true, cells := timerCells none } ]) ++
  [ { pc := 0x8117, x := 0xFF, zOf := none, nOfX := true, cells := timerCells none },
    { pc := 0x8119, x := 0xFF, zOf := none, nOfX := false, cells := timerCells none } ]

theorem table_checks : check decTimersRom table 0x8119 = true := by native_decide

/-- All table entries bound every timer. -/
def tableBounds : Bool :=
  table.all fun b => (List.range 36).all fun n =>
    b.cells.any fun c => c.1 == timerIdx n && all256 fun v => !c.2 v || decide (v ≤ 0x7F)

theorem tableBounds_true : tableBounds = true := by native_decide

/-- A concrete loop entry belongs to the table when all timer bounds are supplied.
This is a local entry condition, not a reachability claim about the game. -/
theorem entry_inv (s : Plain) (n : Nat) (hn : n < 36)
    (hpc : s.regs.pc = 0x810E) (hx : s.regs.x = n.toUInt8)
    (hi : s.regs.p &&& 4 ≠ 0) (hbad : s.bad = false)
    (htimers : ∀ k, k < 36 → s.ram (timerIdx k) ≤ 0x7F) : Inv table s := by
  refine ⟨{ pc := 0x810E, x := n.toUInt8, zOf := none, nOfX := false, cells := timerCells none }, ?_, ?_⟩
  · apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨n, List.mem_range.mpr hn, List.mem_cons_self⟩
  · refine ⟨hpc, hx, hi, hbad, ?_, ?_, ?_⟩
    · intro i h; simp at h
    · intro h; simp at h
    · intro c hc
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
      simpa using htimers k (List.mem_range.mp hk)

theorem inv_timer_le {s : Plain} (h : Inv table s) {n : Nat} (hn : n < 36) : s.ram (timerIdx n) ≤ 0x7F := by
  obtain ⟨b, hb, hh⟩ := h
  have := List.all_eq_true.mp tableBounds_true b hb
  have h2 := List.all_eq_true.mp this n (List.mem_range.mpr hn)
  obtain ⟨c, hc, h3⟩ := List.any_eq_true.mp h2
  simp only [Bool.and_eq_true, beq_iff_eq] at h3
  have h4 := all256_spec h3.2 (s.ram (timerIdx n))
  rw [← h3.1] at h4
  rw [hh.cells c hc] at h4
  rw [h3.1] at h4
  simpa using h4

/-- One real-ROM loop step preserves the invariant and ROM interpretation.
This assumes table membership; it does not establish a legal game entry. -/
theorem decTimers_step {s : Plain} (hc : Code decTimersRom s) (h : Inv table s) (hx : s.regs.pc ≠ 0x8119) :
    Code decTimersRom (CPU.step.run s).2 ∧ Inv table (CPU.step.run s).2 :=
  inv_step table_checks hc h hx

/-- The certificate bounds every timer at each bounded run prefix, including
fuel exhaustion before exit. It does not assert eventual arrival at $8119. -/
theorem decTimers_runTo (fuel : Nat) (s : Plain)
    (hc : Code decTimersRom s) (h : Inv table s) :
    let t := ((CPU.runTo (σ := Plain) 0x8119 fuel).run s).2
    Code decTimersRom t ∧ Inv table t ∧ t.bad = false ∧
      ∀ n, n < 36 → t.ram (timerIdx n) ≤ 0x7F := by
  obtain ⟨hc', h'⟩ := inv_runTo table_checks fuel s hc h
  refine ⟨hc', h', ?_, fun n hn => inv_timer_le h' hn⟩
  obtain ⟨b, _, hb⟩ := h'
  exact hb.bad

/-- A plain state holding the real ROM (which `Rel` gives for the NES) satisfies `Code`. -/
theorem code_of_prg (s : Smb.Plain) (h : ∀ a : UInt16, s.prg (a &&& 0x7FFF) = Smb.prg.get! (a &&& 0x7FFF).toNat) :
    Code decTimersRom s := fun a _ => h a

end Smb.ValueSets
