import Smb.Movement.Model
import Std.Tactic.BVDecide

/-!
# What the check gives

`verified goal T` means that after `T` frames from either start, over every input, progress can't pass `goal`.
-/
namespace Smb.Movement

/-! ## The speed limit -/

theorem capR_ok (v hi c maxr : UInt8) (hv : v ≤ 0x28 ∨ 0xD8 ≤ v) (hh : hi ≤ 1) (hc : c ≤ 1) (hm : maxr = 0x28 ∨ maxr = 0x18 ∨ maxr = 0x10) :
    speedOk (if (v + hi + c - maxr) &&& 0x80 == 0 then maxr else v + hi + c) = true := by
  simp only [speedOk, Bool.or_eq_true, decide_eq_true_eq]
  rcases hm with rfl | rfl | rfl <;> split <;> bv_decide

theorem capL_ok (v hi c maxl : UInt8) (hv : v ≤ 0x28 ∨ 0xD8 ≤ v) (hh : hi ≤ 1) (hc : c ≤ 1) (hm : maxl = 0xD8 ∨ maxl = 0xE8 ∨ maxl = 0xF0) :
    speedOk (if (v - hi - c - maxl) &&& 0x80 == 0 then v - hi - c else maxl) = true := by
  simp only [speedOk, Bool.or_eq_true, decide_eq_true_eq]
  rcases hm with rfl | rfl | rfl <;> split <;> bv_decide

theorem rightV_ok (v f lo hi maxr : UInt8) (hv : speedOk v = true) (hh : hi ≤ 1) (hm : maxr = 0x28 ∨ maxr = 0x18 ∨ maxr = 0x10) :
    speedOk (rightV v f lo hi maxr) = true := by
  simp only [speedOk, Bool.or_eq_true, decide_eq_true_eq] at hv
  exact capR_ok v hi _ maxr hv hh (by split <;> decide) hm

theorem leftV_ok (v f lo hi maxl : UInt8) (hv : speedOk v = true) (hh : hi ≤ 1) (hm : maxl = 0xD8 ∨ maxl = 0xE8 ∨ maxl = 0xF0) :
    speedOk (leftV v f lo hi maxl) = true := by
  simp only [speedOk, Bool.or_eq_true, decide_eq_true_eq] at hv
  exact capL_ok v hi _ maxl hv hh (by split <;> decide) hm

theorem tbl3_r (n : Nat) : tbl3 0x28 0x18 0x10 n = 0x28 ∨ tbl3 0x28 0x18 0x10 n = 0x18 ∨ tbl3 0x28 0x18 0x10 n = 0x10 := by
  match n with
  | 0 => simp [tbl3]
  | 1 => simp [tbl3]
  | _ + 2 => simp [tbl3]

theorem tbl3_l (n : Nat) : tbl3 0xD8 0xE8 0xF0 n = 0xD8 ∨ tbl3 0xD8 0xE8 0xF0 n = 0xE8 ∨ tbl3 0xD8 0xE8 0xF0 n = 0xF0 := by
  match n with
  | 0 => simp [tbl3]
  | 1 => simp [tbl3]
  | _ + 2 => simp [tbl3]

/-- `add`'s high byte is at most 1: the largest step is `$1C8`. -/
theorem add_hi (n : Nat) (c : Prop) [Decidable c] :
    ((if c then ((tbl3 0xE4 0x98 0xD0 n).toUInt16 <<< 1) else (tbl3 0xE4 0x98 0xD0 n).toUInt16) >>> 8).toUInt8 ≤ 1 := by
  have h : tbl3 (0xE4 : UInt8) 0x98 0xD0 n = 0xE4 ∨ tbl3 (0xE4 : UInt8) 0x98 0xD0 n = 0x98 ∨ tbl3 (0xE4 : UInt8) 0x98 0xD0 n = 0xD0 := by
    match n with
    | 0 => simp [tbl3]
    | 1 => simp [tbl3]
    | _ + 2 => simp [tbl3]
  rcases h with h | h | h <;> rw [h] <;> split <;> decide

theorem friction_ok (lr maxr maxl : UInt8) (add : UInt16) (s : S) (hv : speedOk s.v = true) (hh : (add >>> 8).toUInt8 ≤ 1)
    (hr : maxr = 0x28 ∨ maxr = 0x18 ∨ maxr = 0x10) (hl : maxl = 0xD8 ∨ maxl = 0xE8 ∨ maxl = 0xF0) :
    speedOk (friction lr maxr maxl add s).v = true := by
  unfold friction
  split
  · split
    · exact rightV_ok _ _ _ _ _ hv hh hr
    · split
      · exact leftV_ok _ _ _ _ _ hv hh hl
      · exact hv
  · exact hv

/-- The skid check leaves the speed or zeroes it. -/
theorem skid_v (mask lr : UInt8) (s : S) : (skid mask lr s).v = s.v ∨ (skid mask lr s).v = 0 := by
  unfold skid
  dsimp only
  repeat' split
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

theorem routine_ok (rawlr lr a : UInt8) (i : In) (s : S) (hv : speedOk s.v = true) : speedOk (routine rawlr lr a i s).v = true := by
  unfold routine
  split
  · rcases skid_v (rawlr ||| (if i.b then 0x40 else 0) ||| (if i.other || i.down then 0x20 else 0)) lr s with h | h
    · rw [h]; exact hv
    · rw [h]; decide
  · repeat' split
    all_goals exact hv

theorem setMove_v (s : S) : (setMove s).v = s.v := by unfold setMove; split <;> rfl
theorem fallS_v (s : S) : (fallS s).v = s.v := by unfold fallS; split <;> rfl
theorem land_v (g : UInt8) (s : S) : (land g s).v = s.v := by unfold land; split <;> rfl
theorem jumpStart_v (a : UInt8) (s : S) : (jumpStart a s).v = s.v := by unfold jumpStart; split <;> rfl
theorem timerSet_v (lr : UInt8) (b : Bool) (s : S) : (timerSet lr b s).v = s.v := by unfold timerSet; split <;> rfl

theorem norm_v (m : Mode) (s : S) : (norm m s).v = s.v := by
  unfold norm
  repeat' split
  all_goals rfl

theorem step_v (m : Mode) (g : UInt8) (l : Bool) (i : In) (s : S) : (step m g l i s).v = (rawStep g i s).v := by
  simp only [step, norm_v]
  generalize rawStep g i s = t
  split <;> rfl

/-- Speed stays in range. -/
theorem step_ok (m : Mode) (g : UInt8) (l : Bool) (i : In) (s : S) (hv : speedOk s.v = true) : speedOk (step m g l i s).v = true := by
  have h : speedOk (rawStep g i s).v = true := by
    simp only [rawStep, land_v, fallS_v, preFall, moved, setMove_v]
    apply friction_ok
    · apply routine_ok
      rw [timerSet_v, jumpStart_v]
      exact hv
    · exact add_hi _ _
    · exact tbl3_r _
    · exact tbl3_l _
  rw [step_v]
  exact h

/-- In range, a frame moves at most 2.5 pixels either way. -/
theorem adv_le (s : S) (hv : speedOk s.v = true) : adv s ≤ 640 ∧ -640 ≤ adv s := by
  have e1 : (0x28 : UInt8).toNat = 40 := rfl
  have e2 : (0xD8 : UInt8).toNat = 216 := rfl
  have e3 : (0x80 : UInt8).toNat = 128 := rfl
  have hlt := s.v.toNat_lt
  simp only [speedOk, Bool.or_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le, e1, e2] at hv
  simp only [adv, signed, UInt8.lt_iff_toNat_lt, e3]
  split <;> omega

theorem next_ok (m : Mode) (o : Frame) (s : S) (hv : speedOk s.v = true) : speedOk (nextS m o s).v = true := by
  cases o with
  | still => exact hv
  | go g l i => exact step_ok m g l i s hv

theorem delta_le (m : Mode) (o : Frame) (s : S) (hv : speedOk s.v = true) : delta m o s ≤ 640 ∧ -640 ≤ delta m o s := by
  cases o with
  | still => simp [delta]
  | go g l i => exact adv_le _ (step_ok m g l i s hv)

/-! ## Runs -/

/-- A run's end state and progress. -/
def run (m : Mode) : List Frame → S → Int → S × Int
  | [], s, p => (s, p)
  | o :: r, s, p => run m r (nextS m o s) (p + delta m o s)

/-- Every frame of a run is allowed where it happens. -/
def RunOk (m : Mode) : List Frame → S → Int → Prop
  | [], _, _ => True
  | o :: r, s, p => o.allowed m s p ∧ RunOk m r (nextS m o s) (p + delta m o s)

theorem runOk_append (m : Mode) (a b : List Frame) (s : S) (p : Int) (h1 : RunOk m a s p) (h2 : RunOk m b (run m a s p).1 (run m a s p).2) :
    RunOk m (a ++ b) s p := by
  induction a generalizing s p with
  | nil => exact h2
  | cons o r ih => exact ⟨h1.1, ih _ (p + delta m o s) h1.2 h2⟩

theorem run_append (m : Mode) (a b : List Frame) (s : S) (p : Int) : run m (a ++ b) s p = run m b (run m a s p).1 (run m a s p).2 := by
  induction a generalizing s p with
  | nil => rfl
  | cons o r ih => exact ih _ _

/-- From a state in range, progress changes by at most 640 a frame. -/
theorem run_le (m : Mode) (l : List Frame) (s : S) (p : Int) (hv : speedOk s.v = true) :
    (run m l s p).2 ≤ p + 640 * (l.length : Int) ∧ p - 640 * (l.length : Int) ≤ (run m l s p).2 := by
  induction l generalizing s p with
  | nil => simp [run]
  | cons o r ih =>
    have h1 := next_ok m o s hv
    have h2 := delta_le m o s hv
    have h3 := ih (nextS m o s) (p + delta m o s) h1
    simp only [run, List.length_cons]
    push_cast
    omega

/-- Every `In` acts as one in `inputs`. -/
def normal (i : In) : In := if i.down then { i with other := false } else i

theorem rawStep_normal (g : UInt8) (i : In) (s : S) : rawStep g (normal i) s = rawStep g i s := by
  obtain ⟨r, l, b, a, o, d, t⟩ := i
  cases o <;> cases d <;> rfl

theorem normal_mem (i : In) : normal i ∈ inputs := by
  obtain ⟨r, l, b, a, o, d, t⟩ := i
  cases r <;> cases l <;> cases b <;> cases a <;> cases o <;> cases d <;> cases t <;> simp [normal, inputs]

def airIn (i : In) : In := ⟨i.r, i.l, false, i.a, false, false, i.timer⟩

theorem airIn_mem (i : In) : airIn i ∈ airInputs := by
  obtain ⟨r, l, b, a, o, d, t⟩ := i
  cases r <;> cases l <;> cases a <;> cases t <;> simp [airIn, airInputs]

/-- In the air, the other buttons do nothing. -/
theorem rawStep_air (g : UInt8) (i : In) (s : S) (h : (s.st == 0) = false) : rawStep g (airIn i) s = rawStep g i s := by
  have hp : ∀ x : UInt8, preFall (airIn i) { s with t783 := x } = preFall i { s with t783 := x } := by
    intro x
    have ht : (({ s with t783 := x } : S).st == 0) = false := h
    generalize ({ s with t783 := x } : S) = t at ht
    have hj : ∀ a : UInt8, jumpStart a t = t := by
      intro a
      simp [jumpStart, ht]
    have h4 : ∀ x, speedClass x i.b t = speedClass x false t := by
      intro x
      simp [speedClass, running, ht]
    have h5 : ∀ x, frictionClass x i.b t = frictionClass x false t := by
      intro x
      simp [frictionClass, running, ht]
    have h6 : ∀ x b, timerSet x b t = t := by
      intro x b
      simp [timerSet, ht]
    have h7 : ∀ x y z, routine x y z i t = routine x y z ⟨i.r, i.l, false, i.a, false, false, i.timer⟩ t := by
      intro x y z
      simp [routine, ht]
    simp only [preFall, moved, airIn, hj, ht, Bool.and_false, Bool.false_eq_true, if_false, h4, h5, h6, h7]
    rfl
  simp only [rawStep, hp]
  rfl

def normalF (s : S) : Frame → Frame
  | .still => .still
  | .go g l i => .go g l (if s.st == 0 then normal i else airIn i)

theorem floor_mem (m : Mode) (g : UInt8) (p p' : Int) (hp : p ≤ p') (h : g = m.top ∨ (g = m.low ∧ m.walkAt ≤ p)) : g ∈ m.floors p' := by
  unfold Mode.floors
  split
  · rename_i hc
    rcases h with rfl | ⟨rfl, _⟩ <;> simp
  · rename_i hc
    rcases h with rfl | ⟨rfl, h2⟩
    · simp
    · have h3 : m.walkAt ≤ p' := by omega
      simpa [h3] using hc

theorem normalF_mem (m : Mode) (s : S) (p p' : Int) (hp : p ≤ p') (o : Frame) (h : o.allowed m s p) : normalF s o ∈ frames m s p' := by
  cases o with
  | still => simp [normalF, frames]
  | go g l i =>
    obtain ⟨h1, h2⟩ := h
    refine List.mem_cons_of_mem _ ?_
    have hg := floor_mem m g p p' hp h1
    by_cases hs : (s.st == 0) = true
    · simp only [normalF, hs, if_true]
      refine List.mem_flatMap.2 ⟨g, hg, List.mem_flatMap.2 ⟨l, ?_, List.mem_map.2 ⟨_, normal_mem i, rfl⟩⟩⟩
      cases l with
      | false => split <;> simp
      | true =>
        obtain ⟨h3, _, h5⟩ := h2 rfl
        have h6 : m.walkAt ≤ p' := by omega
        simp [h3, h6]
    · have hs' : (s.st == 0) = false := by simpa using hs
      cases l with
      | true => exact absurd (by simpa using (h2 rfl).2.1) hs
      | false =>
        simp only [normalF, hs', if_false, Bool.false_eq_true]
        exact List.mem_flatMap.2 ⟨g, hg, List.mem_map.2 ⟨_, airIn_mem i, rfl⟩⟩

theorem step_normalF (m : Mode) (g : UInt8) (l : Bool) (i : In) (s : S) :
    step m g l (if s.st == 0 then normal i else airIn i) s = step m g l i s := by
  by_cases hs : (s.st == 0) = true
  · simp only [hs, if_true, step, rawStep_normal]
  · have hs' : (s.st == 0) = false := by simpa using hs
    simp only [hs', if_false, Bool.false_eq_true, step, rawStep_air g i s hs']

theorem next_normal (m : Mode) (s : S) (o : Frame) : nextS m (normalF s o) s = nextS m o s := by
  cases o with
  | still => rfl
  | go g l i => simp only [normalF, nextS, step_normalF]

theorem delta_normal (m : Mode) (s : S) (o : Frame) : delta m (normalF s o) s = delta m o s := by
  cases o with
  | still => rfl
  | go g l i => simp only [normalF, delta, step_normalF]

/-! ## The check -/

theorem foldl_mem (L : List (S × Int)) (m0 : Std.HashMap S Int) {t : S} {r : Int}
    (h : (L.foldl (fun m e => m.insert e.1 e.2) m0)[t]? = some r) : m0[t]? = some r ∨ (t, r) ∈ L := by
  induction L generalizing m0 with
  | nil => exact Or.inl h
  | cons a L ih =>
    rcases ih _ h with h1 | h1
    · rw [Std.HashMap.getElem?_insert] at h1
      split at h1
      · rename_i he
        have h2 : a.1 = t := eq_of_beq he
        have h3 : a.2 = r := Option.some.inj h1
        right
        rw [List.mem_cons]
        left
        cases a
        simp_all
      · exact Or.inl h1
    · exact Or.inr (List.mem_cons_of_mem _ h1)

theorem mem_of_map {n : Layer} {t : S} {r : Int}
    (h : (n.foldl (fun m e => m.insert e.1 e.2) ({} : Std.HashMap S Int))[t]? = some r) : (t, r) ∈ n.toList := by
  rw [← Array.foldl_toList] at h
  rcases foldl_mem _ _ h with h1 | h1
  · simp at h1
  · exact h1

theorem layerOk_elim {md : Mode} {goal : Int} {left : Nat} {c n : Layer} (h : layerOk md goal left c n = true) {e : S × Int} (he : e ∈ c.toList) :
    speedOk e.1.v = true ∧
      ∀ o ∈ frames md e.1 e.2, stepOk md goal left (n.foldl (fun m e => m.insert e.1 e.2) {}) e.1 e.2 o = true := by
  simp only [layerOk] at h
  rw [← Array.all_toList, List.all_eq_true] at h
  have h1 := h e he
  simp only [Bool.and_eq_true, List.all_eq_true] at h1
  exact h1

theorem not_mem_of_last {c : Layer} (h : (([c] : List Layer).getLast?.map (·.isEmpty)).getD false = true) {e : S × Int} :
    e ∉ c.toList := by
  have h1 : c.isEmpty = true := by simpa using h
  have h2 : c = #[] := by simpa using h1
  simp [h2]

/-- A chain of layers ending in an empty one bounds every run from a listed state. -/
theorem chain_sound (md : Mode) (goal : Int) : ∀ (left : Nat) (c : Layer) (ls : List Layer),
    chainOk md goal left (c :: ls) = true →
    (((c :: ls).getLast?).map (·.isEmpty)).getD false = true →
    ∀ (l : List Frame), l.length = left → ∀ e ∈ c.toList, ∀ p, p ≤ e.2 → RunOk md l e.1 p → (run md l e.1 p).2 ≤ goal := by
  intro left
  induction left with
  | zero =>
    intro c ls hc hlast l hl e he p hp ha
    cases ls with
    | nil => exact absurd he (not_mem_of_last hlast)
    | cons n r => simp [chainOk] at hc
  | succ left ih =>
    intro c ls hc hlast l hl e he p hp ha
    cases ls with
    | nil => exact absurd he (not_mem_of_last hlast)
    | cons n r =>
      simp only [chainOk, Bool.and_eq_true] at hc
      obtain ⟨hl1, hc2⟩ := hc
      cases l with
      | nil => simp at hl
      | cons o rest =>
        have hlen : rest.length = left := by simpa using hl
        obtain ⟨hv, hall⟩ := layerOk_elim hl1 he
        have hi := hall _ (normalF_mem md e.1 p e.2 hp o ha.1)
        rw [stepOk, next_normal, delta_normal] at hi
        simp only [run]
        have ht := next_ok md o e.1 hv
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hi
        rcases hi with hi | hi
        · have h3 := (run_le md rest _ (p + delta md o e.1) ht).1
          rw [hlen] at h3
          omega
        · split at hi
          · rename_i r0 hr
            have hm := mem_of_map hr
            have hq : e.2 + delta md o e.1 ≤ r0 := by simpa using hi
            refine ih n r hc2 ?_ rest hlen _ hm _ (by simpa using by omega) ha.2
            simpa using hlast
          · simp at hi

/-- The check's meaning: no run of `T` frames from a listed state gets past `goal`. -/
theorem verified_sound (md : Mode) (st : Layer) (goal : Int) (T : Nat) (h : verified md st goal T = true) (l : List Frame) (hl : l.length = T)
    (e : S × Int) (he : e ∈ st.toList) (ha : RunOk md l e.1 e.2) : (run md l e.1 e.2).2 ≤ goal := by
  unfold verified at h
  generalize layers md st goal T = ls at h
  cases ls with
  | nil => simp at h
  | cons c r =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact chain_sound md goal T c r h2 h3 l hl e (by rw [h1]; exact he) _ (Int.le_refl _) ha

end Smb.Movement
