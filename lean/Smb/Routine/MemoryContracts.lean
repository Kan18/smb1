import Smb.Routine.MovePlayerHorizontally
import Smb.Routine.BlockBuffer

/-!
# Small memory contracts for composing routine proofs

These facts project the existing movement and block-buffer summaries. A byte outside
an output's footprint keeps its value; this does not assert that execution never wrote
it. The stack lemmas include all UInt8 stack pointers, including wraparound.
-/
namespace Smb.Routine.MemoryContracts

abbrev stackCell (sp : UInt8) : UInt16 := (0x100 ||| sp.toUInt16) &&& 0x7FF

/-- Project the frame fact already proved by the object routine theorem. -/
theorem object_preserves {x sp : UInt8} {ram : UInt16 → UInt8} {cyc : UInt64} {t : Plain}
    (h : Summary x sp ram cyc t) (i : UInt16)
    (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2)
    (hf : i ≠ forceIdx x) (hp : i ≠ posIdx x) (hg : i ≠ pageIdx x)
    (hs : i ≠ stackCell sp) : t.ram i = ram i := by
  exact h.2.2.2.2.2.2.2.2 i h0 h1 h2 hf hp hg hs

/-- Complete state-preservation footprint of the existing player summary.
This is value preservation, not an assertion that execution made no write. -/
theorem mphRam_preserves (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16)
    (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2)
    (hf : i ≠ 0x400) (hp : i ≠ 0x86) (hg : i ≠ 0x6D)
    (hs : i ≠ stackCell sp) : mphRam sp ram i = ram i := by
  unfold mphRam
  simp only [stackCell] at hs
  bv_decide

/-- A nonzero offset in the stack page never equals the PHA cell, even on wrap. -/
theorem mphRam_stack (sp k : UInt8) (ram : UInt16 → UInt8) (hk : k ≠ 0) :
    mphRam sp ram (stackCell (sp + k)) = ram (stackCell (sp + k)) := by
  apply mphRam_preserves <;> simp only [stackCell] <;> bv_decide

/-- The four facts needed immediately around OnGround's actual $B366 JSR.
Here sp denotes the callee-entry stack pointer, two below caller-entry S. -/
theorem mphRam_caller (sp : UInt8) (ram : UInt16 → UInt8) :
    mphRam sp ram 0x57 = ram 0x57 ∧
    mphRam sp ram 0x33 = ram 0x33 ∧
    mphRam sp ram (stackCell (sp + 1)) = ram (stackCell (sp + 1)) ∧
    mphRam sp ram (stackCell (sp + 2)) = ram (stackCell (sp + 2)) := by
  refine ⟨?_, ?_, mphRam_stack sp 1 ram (by decide), mphRam_stack sp 2 ram (by decide)⟩
  all_goals apply mphRam_preserves <;> (try simp only [stackCell]) <;> bv_decide

/-- OnGround's STA $06FF also preserves the speed obtained from friction. -/
theorem mphRam_scroll_keeps_speed (sp : UInt8) (ram : UInt16 → UInt8) (scroll : UInt8) :
    (fun i : UInt16 => bif i == 0x6FF then scroll else mphRam sp ram i) 0x57 = ram 0x57 := by
  simpa using (mphRam_caller sp ram).1

/-- On the jumpspring bypass, the summary preserves all RAM, including the stack. -/
theorem mphRam_skipped (sp : UInt8) (ram : UInt16 → UInt8) (h : ram 0x70E ≠ 0) :
    mphRam sp ram = ram := by
  funext i
  unfold mphRam
  bv_decide

/-- Read dependencies of the actual returned pixel displacement. -/
theorem mph_result_congr (r q : UInt16 → UInt8)
    (hs : r 0x57 = q 0x57) (hf : r 0x400 = q 0x400) :
    mphCarry r + mphHi (r 0x57) = mphCarry q + mphHi (q 0x57) := by
  simp only [mphCarry, hs, hf]

/-- Every calculated block-buffer address is above the stack/scratch region.
The bound includes wraparound rows, rather than assuming a visible-screen row. -/
theorem bbAddr_bounds (prg ram : UInt16 → UInt8) (x y : UInt8) :
    0x500 ≤ bbAddr prg ram x y ∧ bbAddr prg ram x y ≤ 0x6CF := by
  unfold bbAddr bbLo bbRow
  generalize bbColumn prg ram x y = col
  generalize bbYPos ram x + bbYAdd prg y = row
  bv_decide

/-- Another collision probe overwrites scratch/stack, but preserves Mario's position
and the entire possible tile-read region. These are the inputs to the next probe. -/
theorem bbRam_keeps_probe_inputs (flag x y sp : UInt8) (prg ram : UInt16 → UInt8)
    (i : UInt16) (hi : i = 0x86 ∨ i = 0xCE ∨ i = 0x6D ∨ (0x500 ≤ i ∧ i ≤ 0x6CF)) :
    bbRam flag x y sp prg ram i = ram i := by
  have hn : i ≠ 2 ∧ i ≠ 3 ∧ i ≠ 4 ∧ i ≠ 5 ∧ i ≠ 6 ∧ i ≠ 7 ∧
      i ≠ stackCell sp ∧ i ≠ stackCell (sp - 1) ∧
      i ≠ stackCell (sp - 2) ∧ i ≠ stackCell (sp - 3) := by
    simp only [stackCell]
    bv_decide
  rcases hn with ⟨h2,h3,h4,h5,h6,h7,hs0,hs1,hs2,hs3⟩
  simp only [stackCell] at hs0 hs1 hs2 hs3
  unfold bbRam
  bv_decide

/-- A Mario probe observes only three position bytes and its bounded tile-read region. -/
theorem bbTile_congr (prg r q : UInt16 → UInt8) (y : UInt8)
    (hx : r 0x86 = q 0x86) (hy : r 0xCE = q 0xCE) (hp : r 0x6D = q 0x6D)
    (ht : ∀ i : UInt16, 0x500 ≤ i → i ≤ 0x6CF → r i = q i) :
    bbTile prg r 0 y = bbTile prg q 0 y := by
  have ha : bbAddr prg r 0 y = bbAddr prg q 0 y := by
    have hx' : bbXPos r 0 = bbXPos q 0 := hx
    have hy' : bbYPos r 0 = bbYPos q 0 := hy
    have hp' : bbPage r 0 = bbPage q 0 := hp
    simp only [bbAddr, bbLo, bbColumn, bbXSum, bbRow, hx', hy', hp']
  have hb := bbAddr_bounds prg q 0 y
  have hm : bbAddr prg q 0 y &&& 0x7FF = bbAddr prg q 0 y := by
    generalize bbAddr prg q 0 y = addr at *
    bv_decide
  unfold bbTile
  rw [ha, hm]
  exact ht _ hb.1 hb.2

/-- Reuse the next lookup's input memory without expanding the preceding probe's writes.
The probes may use different offsets y/k. Their old scratch outputs are not preserved. -/
theorem bbTile_after_probe (flag x y sp k : UInt8) (prg ram : UInt16 → UInt8) :
    bbTile prg (bbRam flag x y sp prg ram) 0 k = bbTile prg ram 0 k := by
  apply bbTile_congr
  · exact bbRam_keeps_probe_inputs flag x y sp prg ram 0x86 (Or.inl rfl)
  · exact bbRam_keeps_probe_inputs flag x y sp prg ram 0xCE (Or.inr (Or.inl rfl))
  · exact bbRam_keeps_probe_inputs flag x y sp prg ram 0x6D (Or.inr (Or.inr (Or.inl rfl)))
  · intro i hlo hhi
    exact bbRam_keeps_probe_inputs flag x y sp prg ram i (Or.inr (Or.inr (Or.inr ⟨hlo,hhi⟩)))

end Smb.Routine.MemoryContracts
