import Smb.Routine.RoutineBounds
import Smb.Routine.PlayLinks

/-!
# No prefix of the player block's run is `bad`

`block_prefix`: from a state in `PlayerCtrl`'s entry box at `$B0E9`, every prefix of the plain run to `$AF01` is not
`bad`, or it passed one of the exits that end normal play (pipe, side pipe, flag, climbing, pit death) at a state
that wasn't. The three checked regions `PlayerCtrl`, `CollisionBounds` and `PlayerPost` cover the block end to end
(`RoutineBounds.links`), and each keeps its invariant along every prefix until one of its exits (`runTo_exits`).
-/
namespace Smb.Routine.BlockPrefix
open Smb Smb.Abs Smb.Routine

theorem runTo_add (A : UInt16) : ∀ (m k : Nat) (s : Plain),
    ((CPU.runTo (σ := Plain) A (m + k)).run s).2 = ((CPU.runTo (σ := Plain) A k).run ((CPU.runTo (σ := Plain) A m).run s).2).2 := by
  intro m
  induction m with
  | zero => intro k s; simp [runTo_zero]
  | succ m ih =>
    intro k s
    by_cases hs : s.regs.pc = A
    · rw [runTo_at A _ s hs, runTo_at A _ s hs, runTo_at A _ s hs]
    · rw [show m + 1 + k = (m + k) + 1 by omega, runTo_succ A _ s hs, runTo_succ A _ s hs]
      exact ih k _

/-- Every prefix of a run from inside a checked region stays inside, or passed one of its exits first, at an
instant of the run. -/
theorem runTo_exits {rom : UInt16 → UInt8} {exit prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    (hchk : check rom exit prot g T = true) (htop : gAt g 0x300 = .top) (htop2 : gAt g 0x340 = .top) (A : UInt16) :
    ∀ (n : Nat) (s : Plain), Code rom s → Inv prot g ram0 T s →
      (Code rom ((CPU.runTo (σ := Plain) A n).run s).2 ∧ Inv prot g ram0 T ((CPU.runTo (σ := Plain) A n).run s).2) ∨
      ∃ m k, m ≤ n ∧ k = n - m ∧ exit ((CPU.runTo (σ := Plain) A m).run s).2.regs.pc = true ∧
        ((CPU.runTo (σ := Plain) A m).run s).2.regs.pc ≠ A ∧ Code rom ((CPU.runTo (σ := Plain) A m).run s).2 ∧ Inv prot g ram0 T ((CPU.runTo (σ := Plain) A m).run s).2 ∧
        ((CPU.runTo (σ := Plain) A n).run s).2 = ((CPU.runTo (σ := Plain) A k).run ((CPU.runTo (σ := Plain) A m).run s).2).2 := by
  intro n
  induction n with
  | zero => intro s hc hi; exact Or.inl ⟨hc, hi⟩
  | succ n ih =>
    intro s hc hi
    by_cases hA : s.regs.pc = A
    · rw [runTo_at A _ s hA]; exact Or.inl ⟨hc, hi⟩
    · cases hx : exit s.regs.pc with
      | true => exact Or.inr ⟨0, n + 1, Nat.zero_le _, by omega, hx, hA, hc, hi, rfl⟩
      | false =>
        have hs := inv_step hchk hc hi hx (assumedOk_of_top htop htop2 _)
        rw [runTo_succ A n s hA]
        rcases ih _ hs.1 hs.2 with h | ⟨m, k, hm, hk, h1, h0, h2, h3, h4⟩
        · exact Or.inl h
        · refine Or.inr ⟨m + 1, k, by omega, by omega, ?_⟩
          rw [runTo_succ A m s hA]
          exact ⟨h1, h0, h2, h3, h4⟩

/-- The bounds of `g` are inside `g'`'s at every cell. -/
def withinG (g g' : Global) : Bool :=
  (List.range 0x800).all fun i => (List.range 256).all fun v =>
    !(gAt g (UInt16.ofNat i)).mem (UInt8.ofNat v) || (gAt g' (UInt16.ofNat i)).mem (UInt8.ofNat v)

theorem widenG {g g' : Global} (hw : withinG g g' = true) (hs : g'.size = 0x800) (i : UInt16) (v : UInt8)
    (h : (gAt g i).mem v = true) : (gAt g' i).mem v = true := by
  by_cases hi : i.toNat < 0x800
  · have h1 := List.all_eq_true.mp hw i.toNat (List.mem_range.mpr hi)
    have h2 := List.all_eq_true.mp h1 v.toNat (List.mem_range.mpr v.toNat_lt)
    simp only [UInt16.ofNat_toNat, UInt8.ofNat_toNat, h, Bool.not_true, Bool.false_or] at h2
    exact h2
  · unfold gAt Array.getD
    rw [dif_neg (by omega)]
    rfl

theorem w_ctrl_bounds : withinG PlayerCtrl.conf.globals CollisionBounds.conf.globals = true := by native_decide
theorem w_bounds_post : withinG CollisionBounds.conf.globals PlayerPost.conf.globals = true := by native_decide
theorem bounds_size : CollisionBounds.conf.globals.size = 0x800 := by native_decide
theorem post_size : PlayerPost.conf.globals.size = 0x800 := by native_decide
theorem bounds_top : gAt CollisionBounds.conf.globals 0x300 = .top := eq_top_of_topB (by native_decide)
theorem bounds_top2 : gAt CollisionBounds.conf.globals 0x340 = .top := eq_top_of_topB (by native_decide)
theorem bounds_exit_eq : CollisionBounds.conf.exit = [0xDE88, 0xDE75, 0xDDFC, 0xB179] := by native_decide

/-- Into the next region: a box inside the next region's entry, under bounds inside its own. -/
theorem hop {prot prot' : UInt16 → Bool} {g g' : Global} {ram0 : UInt16 → UInt8} {b e : Box} {t : Plain}
    (hle : Box.le g b e = true) (hw : withinG g g' = true) (hs : g'.size = 0x800) (h : Holds prot g ram0 b t) :
    Holds prot' g' t.ram e t := by
  have h' : Holds prot g t.ram e t := holds_of_le hle
    { pc := h.pc, sp := h.sp, a := h.a, x := h.x, y := h.y, p := h.p, i := h.i, bad := h.bad, cells := h.cells,
      glob := h.glob, frame := fun _ _ => rfl }
  exact { pc := h'.pc, sp := h'.sp, a := h'.a, x := h'.x, y := h'.y, p := h'.p, i := h'.i, bad := h'.bad,
          cells := h'.cells, glob := fun i => widenG hw hs i _ (h'.glob i), frame := fun _ _ => rfl }

/-- The exits that end normal play. -/
def EndExit (pc : UInt16) : Prop := pc = 0xDEFA ∨ pc = 0xDDFC ∨ pc = 0xDE75 ∨ pc = 0xDE88 ∨ pc = 0xB1B8

/-- **No prefix of the block's run is `bad`**, unless it passed an exit that ends normal play first. -/
theorem block_prefix (st : Plain) (hc : Code (romOf Smb.prg) st) (e : Box) (he : e ∈ PlayerCtrl.conf.entries)
    (hh : Holds PlayerCtrl.conf.protFn PlayerCtrl.conf.globals st.ram e st) (n : Nat) :
    ((CPU.runTo (σ := Plain) 0xAF01 n).run st).2.bad = false ∨
      ∃ m, m ≤ n ∧ EndExit ((CPU.runTo (σ := Plain) 0xAF01 m).run st).2.regs.pc ∧
        ((CPU.runTo (σ := Plain) 0xAF01 m).run st).2.bad = false := by
  have hacc := PlayerCtrlLink.ctrl_accepted
  simp only [PlayerCtrl.accepted, Bool.and_eq_true, List.all_eq_true] at hacc
  have hacc2 := RoutineBounds.bounds_accepted
  simp only [CollisionBounds.accepted, Bool.and_eq_true, List.all_eq_true] at hacc2
  have hacc3 := PlayerSplit.post_accepted
  simp only [PlayerPost.accepted, Bool.and_eq_true, List.all_eq_true] at hacc3
  have hl := RoutineBounds.links_true
  simp only [RoutineBounds.links, Bool.and_eq_true, List.all_eq_true] at hl
  have bad_of {prot : UInt16 → Bool} {g : Global} {ram0 : UInt16 → UInt8} {T : Table} {u : Plain}
      (hi : Inv prot g ram0 T u) : u.bad = false := by
    obtain ⟨_, _, hb⟩ := hi
    exact hb.bad
  -- The routine's region, to `PlayerBGCollision`.
  rcases runTo_exits hacc.1 PlayerCtrlLink.ctrl_top PlayerCtrlLink.ctrl_top2 0xAF01 n st hc
      (inv_of_entry (hacc.2 e he) hh) with ⟨_, hi⟩ | ⟨m1, k1, hm1, hk1, hx1, _, hc1, hi1, he1⟩
  · exact Or.inl (bad_of hi)
  generalize hu1 : ((CPU.runTo (σ := Plain) 0xAF01 m1).run st).2 = u1 at hx1 hc1 hi1 he1
  have hp1 : u1.regs.pc = 0xDC64 := by simpa [Config.C.exitFn, PlayerCtrlLink.ctrl_exit_eq] using hx1
  obtain ⟨b1, hb1, hh1⟩ := hi1
  rw [hp1] at hb1
  obtain ⟨e2, he2, hle2⟩ := List.any_eq_true.mp (hl.1 b1 hb1)
  have hh2 : Holds CollisionBounds.conf.protFn CollisionBounds.conf.globals u1.ram e2 u1 :=
    hop hle2 w_ctrl_bounds bounds_size hh1
  -- The collision code's region, to `PlayerHole`.
  rcases runTo_exits hacc2.1 bounds_top bounds_top2 0xAF01 k1 u1 hc1 (inv_of_entry (hacc2.2 e2 he2) hh2) with
    ⟨_, hi⟩ | ⟨m2, k2, hm2, hk2, hx2, _, hc2, hi2, he2'⟩
  · rw [he1]; exact Or.inl (bad_of hi)
  have hm12 : ((CPU.runTo (σ := Plain) 0xAF01 m2).run u1).2 = ((CPU.runTo (σ := Plain) 0xAF01 (m1 + m2)).run st).2 := by
    rw [runTo_add, hu1]
  have hcases : ∀ a, CollisionBounds.conf.exitFn a = true → a = 0xB179 ∨ EndExit a := by
    intro a h
    simp only [Config.C.exitFn, bounds_exit_eq, List.contains_cons, List.contains_nil, Bool.or_false,
      Bool.or_eq_true, beq_iff_eq] at h
    unfold EndExit
    rcases h with h | h | h | h <;> subst h <;> simp
  rcases hcases _ hx2 with hp2 | hend
  · generalize hu2 : ((CPU.runTo (σ := Plain) 0xAF01 m2).run u1).2 = u2 at hp2 hc2 hi2 he2' hm12
    obtain ⟨b2, hb2, hh2'⟩ := hi2
    rw [hp2] at hb2
    obtain ⟨e3, he3, hle3⟩ := List.any_eq_true.mp (hl.2 b2 hb2)
    have hh3 : Holds PlayerPost.conf.protFn PlayerPost.conf.globals u2.ram e3 u2 :=
      hop hle3 w_bounds_post post_size hh2'
    -- After the routine, to the return into the engine.
    rcases runTo_exits hacc3.1 PlayerSplit.post_top PlayerSplit.post_top2 0xAF01 k2 u2 hc2
        (inv_of_entry (hacc3.2 e3 he3) hh3) with ⟨_, hi⟩ | ⟨m3, k3, hm3, hk3, hx3, hn3, _, hi3, _⟩
    · rw [he1, he2']; exact Or.inl (bad_of hi)
    · have hp3 : ((CPU.runTo (σ := Plain) 0xAF01 m3).run u2).2.regs.pc = 0xB1B8 ∨
          ((CPU.runTo (σ := Plain) 0xAF01 m3).run u2).2.regs.pc = 0xAF01 := by
        simp only [Config.C.exitFn, PlayerSplit.post_exit_eq, List.contains_cons, List.contains_nil, Bool.or_false,
          Bool.or_eq_true, beq_iff_eq] at hx3
        exact hx3
      rcases hp3 with hp3 | hp3
      · refine Or.inr ⟨m1 + m2 + m3, by omega, ?_, ?_⟩
        · rw [runTo_add, ← hm12]; unfold EndExit; exact Or.inr (Or.inr (Or.inr (Or.inr hp3)))
        · rw [runTo_add, ← hm12]; exact bad_of hi3
      · exact absurd hp3 hn3
  · refine Or.inr ⟨m1 + m2, by omega, ?_, ?_⟩
    · rw [← hm12]; exact hend
    · rw [← hm12]; exact bad_of hi2

end Smb.Routine.BlockPrefix
