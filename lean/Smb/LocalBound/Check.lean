import Smb.Game
import Init.Data.Range.Lemmas
import Init.Data.List.Monadic

/-!
# Finite certificates for a supported three-frame local bound

The checker preserves the complete NES state and tests every controller byte in
its first-input range, followed by every possible second input. Controller 2 is
idle. Start, Select, and Left+Right are included; no input equivalence or state
reduction is used. Unsupported execution makes the certificate fail.

The bridge is generic in the entry state. It proves the meaning of the executable
checker without native evaluation, then covers arbitrary input lists of length
less than three. Concrete entry-state certificates are separate optional modules.
-/
namespace Smb.LocalBound

attribute [local irreducible] NES.frame

private theorem scan (xs : List α) (p : α → Bool) :
    (forIn xs (none, ()) (fun a _ =>
      if p a then pure (ForInStep.done (some false, ()))
      else pure (ForInStep.yield (none, ()))) : Id (Option Bool × Unit)) =
      (if xs.any p then (some false, ()) else (none, ())) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.forIn_cons, List.any_cons]
    by_cases hp : p a = true <;> simp [hp, ih] <;> rfl

private theorem scanPlain (xs : List α) (p : α → Bool) :
    (forIn xs (none, ()) (fun a _ =>
      if p a then ForInStep.done (some false, ())
      else ForInStep.yield (none, ())) : Id (Option Bool × Unit)) =
      (if xs.any p then (some false, ()) else (none, ())) := scan xs p

private theorem breakIf (p : Bool) (f : Bool → α) (g : Unit → α) :
    @Break.runK.match_1 Bool (fun _ => α) (if p then some false else none) f g =
    (if p then f false else g ()) := by
  cases p <;> rfl

private theorem joinPlain (p q : Bool) (x y : α) :
    (if p then x else if q then x else y) = (if p || q then x else y) := by
  cases p <;> cases q <;> rfl

/-- Check the empty suffix, first inputs in `[lo, hi)`, all second bytes, and
    the three-neutral-frame winning suffix. Any unsupported state rejects the check. -/
def rangeCertificate (entry : NES) (lo hi : Nat) : Bool := Id.run do
  if finalVictory entry || entry.unmodelled then return false
  for a in [lo:hi] do
    let s := NES.frame (UInt8.ofNat a) 0 entry
    if finalVictory s || s.unmodelled then return false
    for b in [0:256] do
      let t := NES.frame (UInt8.ofNat b) 0 s
      if finalVictory t || t.unmodelled then return false
  let win := NES.runFrames [0, 0, 0] entry
  return finalVictory win && !win.unmodelled


/-- The early-return loops implement ordinary finite Boolean conjunctions. -/
theorem rangeCertificate_eq (entry : NES) (lo hi : Nat) :
    rangeCertificate entry lo hi =
      (!(finalVictory entry || entry.unmodelled) &&
       (List.range' lo (hi - lo)).all (fun a =>
         let s := NES.frame (UInt8.ofNat a) 0 entry
         !(finalVictory s || s.unmodelled) &&
         (List.range' 0 256).all (fun b =>
           let t := NES.frame (UInt8.ofNat b) 0 s
           !(finalVictory t || t.unmodelled))) &&
       (let win := NES.runFrames [0, 0, 0] entry
        finalVictory win && !win.unmodelled)) := by
  simp only [rangeCertificate, Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  simp only [scan]
  dsimp only [Id.run, Bind.bind, Pure.pure]
  simp only [apply_ite]
  simp only [breakIf]
  simp only [joinPlain]
  simp only [scanPlain]
  simp only [apply_ite]
  simp only [breakIf]
  rw [List.all_eq_not_any_not]
  simp only [Bool.not_and, Bool.not_not, List.not_all_eq_any_not]
  generalize (finalVictory entry || entry.unmodelled) = p
  generalize ((List.range' lo (hi - lo)).any _) = q
  generalize (finalVictory (NES.runFrames [0, 0, 0] entry) && !(NES.runFrames [0, 0, 0] entry).unmodelled) = w
  cases p <;> cases q <;> cases w <;> rfl

/-- An unfinished state whose execution remains supported. -/
def Safe (s : NES) : Prop := finalVictory s = false ∧ s.unmodelled = false

/-- A finished state whose execution remains supported. -/
def Win (s : NES) : Prop := finalVictory s = true ∧ s.unmodelled = false

private theorem notBool (p : Bool) : ((!p) = true) ↔ p = false := by
  cases p <;> decide


/-- Extract supportedness and outcome facts from a successful range certificate. -/
theorem rangeCertificate_spec (entry : NES) (lo hi : Nat)
    (h : rangeCertificate entry lo hi = true) :
    Safe entry ∧
    (∀ a, lo ≤ a → a < hi →
      Safe (NES.frame (UInt8.ofNat a) 0 entry) ∧
      ∀ b, b < 256 → Safe (NES.frame (UInt8.ofNat b) 0 (NES.frame (UInt8.ofNat a) 0 entry))) ∧
    Win (NES.runFrames [0, 0, 0] entry) := by
  rw [rangeCertificate_eq] at h
  simp only [Bool.and_eq_true, notBool, Bool.or_eq_false_iff, List.all_eq_true] at h
  rcases h with ⟨⟨he, ha⟩, hw⟩
  refine ⟨he, ?_, hw⟩
  intro a hlo hhi
  have hm : a ∈ List.range' lo (hi - lo) :=
    List.mem_range'.mpr ⟨a - lo, by omega, by omega⟩
  rcases ha a hm with ⟨hs, hb⟩
  refine ⟨hs, ?_⟩
  intro b hblt
  exact hb b (List.mem_range'.mpr ⟨b, hblt, by omega⟩)

attribute [local irreducible] rangeCertificate

/-- Separate the short-list argument from the interpreter to avoid unfolding
    the full NES model during kernel conversion. -/
private theorem shortFold {σ α : Type} (step : σ → α → σ) (P : σ → Prop)
    (entry : σ) (he : P entry)
    (hall : ∀ a : α, P (step entry a) ∧ ∀ b : α, P (step (step entry a) b)) :
    ∀ inputs : List α, inputs.length < 3 → P (inputs.foldl step entry) := by
  intro inputs hlen
  cases inputs with
  | nil => exact he
  | cons a rest =>
    cases rest with
    | nil => exact (hall a).1
    | cons b rest =>
      cases rest with
      | nil => exact (hall a).2 b
      | cons c rest => simp only [List.length_cons] at hlen; omega

/-- The three ranges cover every first byte; each checks all 256 second bytes.
    The result includes every list shorter than three and a supported winning witness. -/
theorem threeRangeBridge (entry : NES)
    (h0 : rangeCertificate entry 0 86 = true)
    (h86 : rangeCertificate entry 86 172 = true)
    (h172 : rangeCertificate entry 172 256 = true) :
    (∀ inputs : List UInt8, inputs.length < 3 → Safe (NES.runFrames inputs entry)) ∧
    Win (NES.runFrames [0, 0, 0] entry) := by
  have h0 := rangeCertificate_spec entry 0 86 h0
  have h86 := rangeCertificate_spec entry 86 172 h86
  have h172 := rangeCertificate_spec entry 172 256 h172
  have hall (a : UInt8) : Safe (NES.frame a 0 entry) ∧
      ∀ b : UInt8, Safe (NES.frame b 0 (NES.frame a 0 entry)) := by
    have ha : a.toNat < 256 := UInt8.toNat_lt a
    have hr : Safe (NES.frame (UInt8.ofNat a.toNat) 0 entry) ∧
        ∀ b, b < 256 → Safe (NES.frame (UInt8.ofNat b) 0 (NES.frame (UInt8.ofNat a.toNat) 0 entry)) := by
      by_cases hlt : a.toNat < 86
      · exact h0.2.1 a.toNat (by omega) hlt
      · by_cases hlt2 : a.toNat < 172
        · exact h86.2.1 a.toNat (by omega) hlt2
        · exact h172.2.1 a.toNat (by omega) ha
    refine ⟨by simpa only [UInt8.ofNat_toNat] using hr.1, ?_⟩
    intro b
    simpa only [UInt8.ofNat_toNat] using hr.2 b.toNat (UInt8.toNat_lt b)
  exact ⟨shortFold (fun s a => NES.frame a 0 s) Safe entry h0.1 hall, h0.2.2⟩

end Smb.LocalBound
