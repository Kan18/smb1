import Smb.Routine.Common

/-!
# Layer C: how often the surface's buffer-1 events can happen

A window is the run of game updates between two buffer-1 clears: the NMI clears buffer 1 unless the update before
it ended with `VRAM_Buffer_AddrCtrl` (`$0773`) at 6. These are the counting arguments, as small automata over the
RAM cells that schedule each event. Each automaton's step is the ROM's (`ScheduleRom` checks the code), and what's
assumed is stated on each: which writers a cell has. That's the stray-store question again, for these cells.

* **The parser.** On the 1-1 surface, only the parser's render tasks set `$0773` to 6, and its 8-task cycle never
  renders on four updates in a row (`no_four_sixes`). So a window is at most 4 updates.
* **Floatey numbers.** A slot awards points only when its timer, counting down from `$30`, passes `$2B`, so one
  slot's awards are at least 6 updates apart (`awards_le_one`): at most one per slot per window.
* **Periodic events.** The game timer prints only when `GameTimerCtrlTimer` has run down from `$18`, and color
  rotation only every eighth frame: at most one each per window (`cooldown_le_one`).
-/
namespace Smb.Buffer.Schedule

/-! ## The parser's task cycle (`AreaParserTaskHandler`, `$92B0`) -/

/-- Whether a parser task index renders: `AreaParserTasks` is `IncrementColumnPos`, `RenderAreaGraphics` twice,
`AreaParserCore`, and again, so tasks 1, 2, 5 and 6 render a column. -/
def taskRenders (i : UInt8) : Bool := i == 1 || i == 2 || i == 5 || i == 6

/-- One update's parser step, from `AreaParserTaskNum` `n`, when nothing earlier in the update set `$0773` to 6.
`start` is whether `ScrollThirtyTwo` has reached `$20`, which only matters when `n` = 0. It returns the new task
number and whether the update ends with `$0773` at 6: a rendered column, or the attribute tables after task 0. -/
def parserStep (n : UInt8) (start : Bool) : UInt8 × Bool :=
  if n == 0 then
    if start then (7, taskRenders 7) else (0, false)
  else (n - 1, taskRenders (n - 1) || n - 1 == 0)

/-- Four updates from task number `n`, with scroll choices `a`–`d`: whether all four end at 6. -/
def allSix (n : UInt8) (a b c d : Bool) : Bool :=
  let r1 := parserStep n a
  let r2 := parserStep r1.1 b
  let r3 := parserStep r2.1 c
  let r4 := parserStep r3.1 d
  r1.2 && r2.2 && r3.2 && r4.2

/-- **Windows are at most 4 updates.** Without other writers of `$0773`, from any task number the handler can
hold (it sets 8 and counts down), four updates in a row never all end with `$0773` at 6, so the NMI clears buffer 1
at least once in any four. -/
theorem no_four_sixes (n : UInt8) (hn : n ≤ 8) (a b c d : Bool) : allSix n a b c d = false := by
  have h : ∀ i : Fin 9, ∀ a b c d : Bool, allSix (UInt8.ofNat i) a b c d = false := by decide
  have hn' : n.toNat < 9 := by have := UInt8.le_iff_toNat_le.mp hn; simp at this; omega
  simpa using h ⟨n.toNat, hn'⟩ a b c d

/-- The handler keeps its task number at 8 or below. -/
theorem parserStep_le (n : UInt8) (hn : n ≤ 8) (start : Bool) : (parserStep n start).1 ≤ 8 := by
  unfold parserStep
  cases h : n == 0 <;> cases start <;> simp only [h, if_true, if_false, Bool.false_eq_true] <;>
    first | decide | (simp only [beq_eq_false_iff_ne, ne_eq] at h; revert hn h; bv_decide)

/-! ## A floatey-number slot (`FloateyNumbersRoutine`, `$84C3`; `SetupFloateyNumber`, `$DA11`) -/

/-- What can happen to one slot in an update: a `SetupFloateyNumber` before the slot's routine runs, the routine
itself (whether it ran, and whether its control byte was nonzero; zero freezes the timer), and a setup after it. -/
structure SlotUpdate where
  setupBefore : Bool
  called : Bool
  active : Bool
  setupAfter : Bool

/-- The timer the routine reads: `$30` if a setup came first. -/
def slotT1 (u : SlotUpdate) (t : UInt8) : UInt8 := if u.setupBefore then 0x30 else t

/-- Whether the routine ran this update (frozen or not). -/
def slotCalled (u : SlotUpdate) : Bool := u.called

/-- Whether the routine awards: active, and it read `$2B`. -/
def slotAw (u : SlotUpdate) (t : UInt8) : Bool := u.called && u.active && slotT1 u t == 0x2B

/-- The timer after the update. An active call decrements a nonzero timer; a later setup sets `$30`. -/
def slotT (u : SlotUpdate) (t : UInt8) : UInt8 :=
  if u.setupAfter then 0x30
  else if u.called && u.active && !(slotT1 u t == 0) then slotT1 u t - 1 else slotT1 u t

/-- The calls since the last award, capped at 5. -/
def slotK (u : SlotUpdate) (t k : UInt8) : UInt8 :=
  if slotAw u t then 0 else if slotCalled u then (if k < 5 then k + 1 else 5) else k

/-- One update of a slot: the new timer and count, and whether the slot awarded points (called `AddToScore`). The
routine (`$84C3`) decrements a nonzero timer when its control byte is nonzero, and awards when the timer it read
was `$2B`; `SetupFloateyNumber` sets the timer to `$30`. Those are the timer's only writers. -/
def slotStep (u : SlotUpdate) (t k : UInt8) : UInt8 × UInt8 × Bool := (slotT u t, slotK u t k, slotAw u t)

/-- The invariant: a timer between `$2B` and `$30` has had at least `$30 - t` calls since the last award, and one
above `$30` (only possible before any setup) has had no award yet in view. -/
def SlotInv (t k : UInt8) : Prop :=
  k ≤ 5 ∧ (0x2B ≤ t → t ≤ 0x30 → 0x30 ≤ k + t) ∧ (0x30 < t → k = 5)

theorem slotInv_start (t : UInt8) : SlotInv t 5 := by
  unfold SlotInv; bv_decide

set_option maxHeartbeats 4000000 in
/-- One update keeps the invariant; an award needs 5 calls since the last one, and resets the count; otherwise the
count rises by at most one. -/
theorem slotStep_inv (u : SlotUpdate) (t k : UInt8) (h : SlotInv t k) :
    SlotInv (slotT u t) (slotK u t k) ∧ (slotAw u t = true → k = 5 ∧ slotK u t k = 0) ∧
      (slotAw u t = false → slotK u t k ≤ k + 1) := by
  obtain ⟨sb, c, a, sa⟩ := u
  unfold SlotInv at h ⊢
  cases sb <;> cases sa <;> cases c <;> cases a <;>
    simp only [slotT, slotK, slotAw, slotT1, slotCalled, Bool.false_eq_true, if_true, if_false, Bool.true_and,
      Bool.false_and, Bool.and_true, Bool.and_false] <;> revert h <;> bv_decide

theorem toNat_le_succ {a k : UInt8} (hk : k ≤ 5) (h : a ≤ k + 1) : a.toNat ≤ k.toNat + 1 := by
  have h1 := UInt8.le_iff_toNat_le.mp h
  have h2 := UInt8.le_iff_toNat_le.mp hk
  rw [UInt8.toNat_add] at h1
  simp only [UInt8.toNat_ofNat] at h1 h2
  omega

/-- The awards over a list of updates, from timer `t` and count `k`. -/
def slotAwards : List SlotUpdate → UInt8 → UInt8 → Nat
  | [], _, _ => 0
  | u :: us, t, k => (if slotAw u t then 1 else 0) + slotAwards us (slotT u t) (slotK u t k)

/-- With fewer than `5 - k` updates left, no award. -/
theorem slotAwards_zero : ∀ (us : List SlotUpdate) (t k : UInt8), SlotInv t k → k.toNat + us.length ≤ 5 →
    slotAwards us t k = 0
  | [], _, _, _, _ => rfl
  | u :: us, t, k, h, hl => by
    have hs := slotStep_inv u t k h
    simp only [List.length_cons] at hl
    simp only [slotAwards]
    cases haw : slotAw u t
    · simp only [Bool.false_eq_true, if_false, Nat.zero_add]
      exact slotAwards_zero us _ _ hs.1 (by have := toNat_le_succ h.1 (hs.2.2 haw); omega)
    · obtain ⟨rfl, _⟩ := hs.2.1 haw
      simp at hl; omega

/-- **At most one award per slot in any 6 updates**, from any state the invariant allows. -/
theorem awards_le_one : ∀ (us : List SlotUpdate) (t k : UInt8), SlotInv t k → us.length ≤ 6 →
    slotAwards us t k ≤ 1
  | [], _, _, _, _ => Nat.zero_le _
  | u :: us, t, k, h, hl => by
    have hs := slotStep_inv u t k h
    simp only [List.length_cons] at hl
    simp only [slotAwards]
    cases haw : slotAw u t
    · simp only [Bool.false_eq_true, if_false, Nat.zero_add]
      exact awards_le_one us _ _ hs.1 (by omega)
    · obtain ⟨_, h0⟩ := hs.2.1 haw
      simp only [if_true]
      rw [slotAwards_zero us _ _ hs.1 (by rw [h0]; simp; omega)]
      omega

/-- From any timer, with no history assumed. -/
theorem awards_le_one_any (us : List SlotUpdate) (t : UInt8) (hl : us.length ≤ 6) : slotAwards us t 5 ≤ 1 :=
  awards_le_one us t 5 (slotInv_start t) hl

/-! ## Periodic events -/

/-- A cooldown counter: an event happens only when the counter is 0, and sets it to `n`; otherwise it falls by at
most one an update. Returns the count of events over the list of choices (`fire`, and how far it falls). -/
def cooldownEvents (n : Nat) : List (Bool × Bool) → Nat → Nat
  | [], _ => 0
  | (fire, dec) :: us, c =>
    if fire && c == 0 then 1 + cooldownEvents n us n else cooldownEvents n us (if dec then c - 1 else c)

theorem cooldown_zero (n : Nat) : ∀ (us : List (Bool × Bool)) (c : Nat), us.length ≤ c → cooldownEvents n us c = 0
  | [], _, _ => rfl
  | (fire, dec) :: us, c, h => by
    simp only [List.length_cons] at h
    simp only [cooldownEvents]
    have hc : (c == 0) = false := by simp; omega
    simp only [hc, Bool.and_false, Bool.false_eq_true, if_false]
    exact cooldown_zero n us _ (by split <;> omega)

/-- **At most one event in `n + 1` updates**: the game timer's print (`GameTimerCtrlTimer`, `n = $18`). -/
theorem cooldown_le_one (n : Nat) : ∀ (us : List (Bool × Bool)) (c : Nat), us.length ≤ n + 1 →
    cooldownEvents n us c ≤ 1
  | [], _, _ => Nat.zero_le _
  | (fire, dec) :: us, c, h => by
    simp only [List.length_cons] at h
    simp only [cooldownEvents]
    split
    · rw [cooldown_zero n us n (by omega)]
      omega
    · exact cooldown_le_one n us _ (by omega)

/-- Color rotation runs only when `FrameCounter &&& 7 = 0`, and the counter rises by one an update: over any 8
updates, it runs at most once. -/
theorem rotation_le_one (f i j : UInt8) (hi : i < 8) (hj : j < 8) (h1 : (f + i) &&& 7 = 0) (h2 : (f + j) &&& 7 = 0) :
    i = j := by
  bv_decide

end Smb.Buffer.Schedule
