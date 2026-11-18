import Lean

/-!
# Literal evaluation for bitwise `UInt8`/`UInt16` operations

Lean's built-in simprocs evaluate `+`, `-`, `*` and comparisons on literal machine integers,
but not bitwise operations or width conversions. Symbolic execution of 6502 code needs them
for address masking (`a &&& 0x7FF`), opcode decoding and pointer assembly. These are not
in the default simp set; `Smb.Routine` names them explicitly.
-/
namespace Smb.Simprocs
open Lean Meta Simp

def u8? (e : Expr) : SimpM (Option UInt8) := do
  let some (n, _) ← getOfNatValue? e ``UInt8 | return none
  return UInt8.ofNat n

def u16? (e : Expr) : SimpM (Option UInt16) := do
  let some (n, _) ← getOfNatValue? e ``UInt16 | return none
  return UInt16.ofNat n

@[inline] def bin8 (declName : Name) (op : UInt8 → UInt8 → UInt8) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName 6 do return .continue
  let some a ← u8? e.appFn!.appArg! | return .continue
  let some b ← u8? e.appArg! | return .continue
  return .done (toExpr (op a b))

@[inline] def bin16 (declName : Name) (op : UInt16 → UInt16 → UInt16) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName 6 do return .continue
  let some a ← u16? e.appFn!.appArg! | return .continue
  let some b ← u16? e.appArg! | return .continue
  return .done (toExpr (op a b))

dsimproc u8and ((_ : UInt8) &&& _) := bin8 ``HAnd.hAnd (· &&& ·)
dsimproc u8or ((_ : UInt8) ||| _) := bin8 ``HOr.hOr (· ||| ·)
dsimproc u8xor ((_ : UInt8) ^^^ _) := bin8 ``HXor.hXor (· ^^^ ·)
dsimproc u8shl ((_ : UInt8) <<< _) := bin8 ``HShiftLeft.hShiftLeft (· <<< ·)
dsimproc u8shr ((_ : UInt8) >>> _) := bin8 ``HShiftRight.hShiftRight (· >>> ·)
dsimproc u16and ((_ : UInt16) &&& _) := bin16 ``HAnd.hAnd (· &&& ·)
dsimproc u16or ((_ : UInt16) ||| _) := bin16 ``HOr.hOr (· ||| ·)
dsimproc u16xor ((_ : UInt16) ^^^ _) := bin16 ``HXor.hXor (· ^^^ ·)
dsimproc u16shl ((_ : UInt16) <<< _) := bin16 ``HShiftLeft.hShiftLeft (· <<< ·)
dsimproc u16shr ((_ : UInt16) >>> _) := bin16 ``HShiftRight.hShiftRight (· >>> ·)

@[inline] def pred8 (declName : Name) (arity : Nat) (op : UInt8 → UInt8 → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some a ← u8? e.appFn!.appArg! | return .continue
  let some b ← u8? e.appArg! | return .continue
  return .done (toExpr (op a b))

@[inline] def pred16 (declName : Name) (arity : Nat) (op : UInt16 → UInt16 → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some a ← u16? e.appFn!.appArg! | return .continue
  let some b ← u16? e.appArg! | return .continue
  return .done (toExpr (op a b))

dsimproc u8beq ((_ : UInt8) == _) := pred8 ``BEq.beq 4 (· == ·)
dsimproc u8bne ((_ : UInt8) != _) := pred8 ``bne 4 (· != ·)
dsimproc u16beq ((_ : UInt16) == _) := pred16 ``BEq.beq 4 (· == ·)
dsimproc u16bne ((_ : UInt16) != _) := pred16 ``bne 4 (· != ·)

/-- Equality of literals as a proposition (so `simp` need not use `decide`, which tries to
evaluate every decidable proposition, including symbolic ones, by unfolding). -/
simproc u8eq ((_ : UInt8) = _) := fun e => do
  unless e.isAppOfArity ``Eq 3 do return .continue
  let some a ← u8? e.appFn!.appArg! | return .continue
  let some b ← u8? e.appArg! | return .continue
  evalPropStep e (a == b)

simproc u16eq ((_ : UInt16) = _) := fun e => do
  unless e.isAppOfArity ``Eq 3 do return .continue
  let some a ← u16? e.appFn!.appArg! | return .continue
  let some b ← u16? e.appArg! | return .continue
  evalPropStep e (a == b)

dsimproc u8not (~~~(_ : UInt8)) := fun e => do
  unless e.isAppOfArity ``Complement.complement 3 do return .continue
  let some a ← u8? e.appArg! | return .continue
  return .done (toExpr (~~~a))

dsimproc u8toU16 (UInt8.toUInt16 _) := fun e => do
  unless e.isAppOfArity ``UInt8.toUInt16 1 do return .continue
  let some a ← u8? e.appArg! | return .continue
  return .done (toExpr a.toUInt16)

dsimproc u16toU8 (UInt16.toUInt8 _) := fun e => do
  unless e.isAppOfArity ``UInt16.toUInt8 1 do return .continue
  let some a ← u16? e.appArg! | return .continue
  return .done (toExpr a.toUInt8)

/-! ### Flags and cycle counts as small closed forms

Every instruction rebuilds `p` from the previous one (`(p &&& 0x7D) ||| N ||| Z`), and every
flag test reads it through a literal mask. Pushing literal masks into such terms keeps only
the latest setter of each flag: a `BMI` after `LDA v` tests `v &&& 0x80` instead of a chain
through every earlier flag value, and the IRQ check reduces to the initial `p &&& 4`.

The rewrites fire only on flag-shaped terms (literals, `t &&& lit`, `cond c lit lit`, and
`|||` of those). Applied to arbitrary values they would also rewrite the `N`/`Z` terms of a
freshly loaded value, which then no longer match the value itself and cannot be abstracted
to its name; that made every `simp` call 20 times slower.

Cycle increments likewise fold into one literal, or a `cond` of literals for page crossings. -/

theorem u8_or_and (a b m : UInt8) : (a ||| b) &&& m = (a &&& m) ||| (b &&& m) := by
  apply UInt8.toBitVec_inj.mp; simp [BitVec.and_or_distrib_right]
theorem u8_and_and (a m n : UInt8) : (a &&& m) &&& n = a &&& (m &&& n) := by
  apply UInt8.toBitVec_inj.mp; simp [BitVec.and_assoc]
theorem u8_and_zero (a : UInt8) : a &&& 0 = 0 := by apply UInt8.toBitVec_inj.mp; simp
theorem u8_or_zero (a : UInt8) : a ||| 0 = a := by apply UInt8.toBitVec_inj.mp; simp
theorem u8_zero_or (a : UInt8) : 0 ||| a = a := by apply UInt8.toBitVec_inj.mp; simp
theorem u8_cond_and (c : Bool) (a b m : UInt8) : (cond c a b) &&& m = cond c (a &&& m) (b &&& m) := by
  cases c <;> rfl
theorem u8_cond_bne (c : Bool) (a b k : UInt8) : (cond c a b != k) = cond c (a != k) (b != k) := by
  cases c <;> rfl
theorem u8_cond_beq (c : Bool) (a b k : UInt8) : (cond c a b == k) = cond c (a == k) (b == k) := by
  cases c <;> rfl
theorem u8_cond_toU16 (c : Bool) (a b : UInt8) : (cond c a b).toUInt16 = cond c a.toUInt16 b.toUInt16 := by
  cases c <;> rfl
theorem cond_true_false' (c : Bool) : cond c true false = c := by cases c <;> rfl
theorem cond_false_true' (c : Bool) : cond c false true = !c := by cases c <;> rfl
theorem u64_add_assoc (a b c : UInt64) : a + b + c = a + (b + c) := UInt64.add_assoc a b c
theorem u64_cond_add (c : Bool) (a b k : UInt64) : cond c a b + k = cond c (a + k) (b + k) := by
  cases c <;> rfl
theorem u64_add_cond (c : Bool) (a b k : UInt64) : k + cond c a b = cond c (k + a) (k + b) := by
  cases c <;> rfl

def u64? (e : Expr) : SimpM (Option UInt64) := do
  let some (n, _) ← getOfNatValue? e ``UInt64 | return none
  return UInt64.ofNat n

/-- `cond c lit lit`, at any width. -/
def isCondLit (e : Expr) : SimpM Bool := do
  unless e.isAppOfArity ``cond 4 do return false
  let some ty := (e.getArg! 0).constName? | return false
  return (← getOfNatValue? (e.getArg! 2) ty).isSome && (← getOfNatValue? (e.getArg! 3) ty).isSome

partial def flagShaped (e : Expr) : SimpM Bool := do
  if (← u8? e).isSome then return true
  if e.isAppOfArity ``HAnd.hAnd 6 then return (← u8? e.appArg!).isSome
  -- `ASL`/`ROL` carry out: bit 7 of the old value.
  if e.isAppOfArity ``HShiftRight.hShiftRight 6 then return (← u8? e.appArg!) == some 7
  if e.isAppOfArity ``HOr.hOr 6 then
    return (← flagShaped e.appFn!.appArg!) && (← flagShaped e.appArg!)
  isCondLit e

@[inline] def rewriteWith (thm : Name) (args : Array Expr) : SimpM Step := do
  let proof := mkAppN (mkConst thm) args
  let some (_, _, rhs) := (← inferType proof).eq? | return .continue
  return .visit { expr := rhs, proof? := some proof }

theorem u8_shr7_and (t m : UInt8) : (t >>> 7) &&& m = (t >>> 7) &&& (m &&& 1) := by
  apply UInt8.toBitVec_inj.mp
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_shiftRight]
  ext i hi
  simp only [BitVec.getElem_and]
  by_cases h0 : i = 0
  · subst h0; simp
  · have : 7 + i ≥ 8 := by omega
    simp [this]

/-- `(t >>> 7) &&& m` only keeps bit 0 of `m`. -/
simproc shr7Mask (((_ : UInt8) >>> 7) &&& _) := fun e => do
  unless e.isAppOfArity ``HAnd.hAnd 6 do return .continue
  let some m ← u8? e.appArg! | return .continue
  if m &&& 1 == m then return .continue
  let t := e.appFn!.appArg!
  unless t.isAppOfArity ``HShiftRight.hShiftRight 6 && (← u8? t.appArg!) == some 7 do return .continue
  rewriteWith ``u8_shr7_and #[t.appFn!.appArg!, e.appArg!]

/-- `(a ||| b) &&& lit`, flag-shaped `a ||| b`. -/
simproc maskOr (((_ : UInt8) ||| _) &&& _) := fun e => do
  unless e.isAppOfArity ``HAnd.hAnd 6 do return .continue
  let some _ ← u8? e.appArg! | return .continue
  let ab := e.appFn!.appArg!
  unless ab.isAppOfArity ``HOr.hOr 6 && (← flagShaped ab) do return .continue
  rewriteWith ``u8_or_and #[ab.appFn!.appArg!, ab.appArg!, e.appArg!]

/-- `(a &&& lit) &&& lit`, when that cannot hide a value's own `N`/`Z` term. -/
simproc maskAnd (((_ : UInt8) &&& _) &&& _) := fun e => do
  unless e.isAppOfArity ``HAnd.hAnd 6 do return .continue
  let some n ← u8? e.appArg! | return .continue
  let am := e.appFn!.appArg!
  unless am.isAppOfArity ``HAnd.hAnd 6 do return .continue
  let some m ← u8? am.appArg! | return .continue
  -- A variable's mask, disjoint masks (→ 0), or an outer mask that changes nothing.
  unless am.appFn!.appArg!.isFVar || m &&& n == 0 || m &&& n == m do return .continue
  rewriteWith ``u8_and_and #[am.appFn!.appArg!, am.appArg!, e.appArg!]

simproc maskCond ((cond _ (_ : UInt8) _) &&& _) := fun e => do
  unless e.isAppOfArity ``HAnd.hAnd 6 do return .continue
  let some _ ← u8? e.appArg! | return .continue
  let c := e.appFn!.appArg!
  unless (← isCondLit c) do return .continue
  rewriteWith ``u8_cond_and #[c.getArg! 1, c.getArg! 2, c.getArg! 3, e.appArg!]

simproc condBeq ((cond _ (_ : UInt8) _) == _) := fun e => do
  unless e.isAppOfArity ``BEq.beq 4 do return .continue
  let some _ ← u8? e.appArg! | return .continue
  let c := e.appFn!.appArg!
  unless (← isCondLit c) do return .continue
  rewriteWith ``u8_cond_beq #[c.getArg! 1, c.getArg! 2, c.getArg! 3, e.appArg!]

simproc condBne ((cond _ (_ : UInt8) _) != _) := fun e => do
  unless e.isAppOfArity ``bne 4 do return .continue
  let some _ ← u8? e.appArg! | return .continue
  let c := e.appFn!.appArg!
  unless (← isCondLit c) do return .continue
  rewriteWith ``u8_cond_bne #[c.getArg! 1, c.getArg! 2, c.getArg! 3, e.appArg!]

simproc condToU16 (UInt8.toUInt16 (cond _ _ _)) := fun e => do
  unless e.isAppOfArity ``UInt8.toUInt16 1 do return .continue
  let c := e.appArg!
  unless (← isCondLit c) do return .continue
  rewriteWith ``u8_cond_toU16 #[c.getArg! 1, c.getArg! 2, c.getArg! 3]

theorem ite_eq_cond {c : Prop} [h : Decidable c] (a b : α) : @ite α c h a b = cond (@decide c h) a b := by
  cases h <;> rfl
theorem ite_or_self {c : Prop} [Decidable c] (x f : UInt8) : (if c then x ||| f else x) = x ||| (if c then f else 0) := by
  split <;> simp
theorem ite_or_andnot {c : Prop} [Decidable c] (x f : UInt8) :
    (if c then x ||| f else x &&& ~~~f) = (x &&& ~~~f) ||| (if c then f else 0) := by
  split
  · apply UInt8.toBitVec_inj.mp; simp only [UInt8.toBitVec_or, UInt8.toBitVec_and, UInt8.toBitVec_not]
    ext i; simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]; cases x.toBitVec[i] <;> cases f.toBitVec[i] <;> rfl
  · simp
theorem cond_or_self (c : Bool) (x f : UInt8) : cond c (x ||| f) x = x ||| cond c f 0 := by
  cases c <;> simp

/-- `if c then lit else lit` → `cond (decide c) lit lit`, so the flag rewrites see it. -/
simproc iteLit (@ite UInt8 _ _ _ _) := fun e => do
  unless e.isAppOfArity ``ite 5 do return .continue
  let some _ ← u8? (e.getArg! 3) | return .continue
  let some _ ← u8? (e.getArg! 4) | return .continue
  let rhs := mkApp4 (mkConst ``cond [Level.one]) (e.getArg! 0)
    (mkApp2 (mkConst ``decide) (e.getArg! 1) (e.getArg! 2)) (e.getArg! 3) (e.getArg! 4)
  let pf := mkApp5 (mkConst ``ite_eq_cond [Level.one]) (e.getArg! 0) (e.getArg! 1) (e.getArg! 2)
    (e.getArg! 3) (e.getArg! 4)
  return .visit { expr := rhs, proof? := some pf }

/-- Setting one flag conditionally: `if c then x ||| f else x` (ADC's carry) and
`if c then x ||| f else x &&& ~f` (CMP's carry) → `x' ||| (if c then f else 0)`. Without this
each such instruction copies the whole previous flags term into both branches. -/
simproc iteFlag (@ite UInt8 _ _ (_ ||| _) _) := fun e => do
  unless e.isAppOfArity ``ite 5 do return .continue
  let t := e.getArg! 3
  let el := e.getArg! 4
  unless t.isAppOfArity ``HOr.hOr 6 do return .continue
  let x := t.appFn!.appArg!
  let some f ← u8? t.appArg! | return .continue
  -- Built directly: `mkAppM` would type-check the instance under simp's reducible setting.
  let (c, inst) := (e.getArg! 1, e.getArg! 2)
  let bit := mkApp5 (mkConst ``ite [Level.one]) (mkConst ``UInt8) c inst t.appArg! (toExpr (0 : UInt8))
  let orOp := t.appFn!.appFn!
  if el == x then
    let pf := mkApp4 (mkConst ``ite_or_self) c inst x t.appArg!
    return .visit { expr := mkApp2 orOp x bit, proof? := some pf }
  unless el.isAppOfArity ``HAnd.hAnd 6 && el.appFn!.appArg! == x do return .continue
  let some g ← u8? el.appArg! | return .continue
  unless g == ~~~f do return .continue
  let rhs := mkApp2 orOp el bit
  let pf ← mkExpectedTypeHint (mkApp4 (mkConst ``ite_or_andnot) c inst x t.appArg!) (← mkEq e rhs)
  return .visit { expr := rhs, proof? := some pf }

simproc condFlag (cond _ ((_ : UInt8) ||| _) _) := fun e => do
  unless e.isAppOfArity ``cond 4 do return .continue
  let t := e.getArg! 2
  unless t.isAppOfArity ``HOr.hOr 6 && t.appFn!.appArg! == e.getArg! 3 do return .continue
  let some _ ← u8? t.appArg! | return .continue
  rewriteWith ``cond_or_self #[e.getArg! 1, e.getArg! 3, t.appArg!]

theorem u8_sub_eq (a b : UInt8) : a - b = a + (0 - b) := by
  apply UInt8.toBitVec_inj.mp; simp [BitVec.sub_eq_add_neg]
theorem u8_add_assoc (a b c : UInt8) : a + b + c = a + (b + c) := UInt8.add_assoc a b c

/-- Stack arithmetic in one form, `s + k` (literal `k`): `s - k` → `s + (256 - k)`. -/
simproc u8SubLit ((_ : UInt8) - _) := fun e => do
  unless e.isAppOfArity ``HSub.hSub 6 do return .continue
  let some _ ← u8? e.appArg! | return .continue
  if (← u8? e.appFn!.appArg!).isSome then return .continue
  rewriteWith ``u8_sub_eq #[e.appFn!.appArg!, e.appArg!]

/-- `(s + k₁) + k₂` → `s + (k₁ + k₂)` for literals. -/
simproc u8AddLit (((_ : UInt8) + _) + _) := fun e => do
  unless e.isAppOfArity ``HAdd.hAdd 6 do return .continue
  let some _ ← u8? e.appArg! | return .continue
  let sk := e.appFn!.appArg!
  unless sk.isAppOfArity ``HAdd.hAdd 6 do return .continue
  let some _ ← u8? sk.appArg! | return .continue
  rewriteWith ``u8_add_assoc #[sk.appFn!.appArg!, sk.appArg!, e.appArg!]

/-- A cycle increment: a literal or a `cond` of literals. -/
def isInc (e : Expr) : SimpM Bool := do
  if (← u64? e).isSome then return true
  isCondLit e

/-- `x + i + j` with increments `i`, `j` → `x + (i + j)`. -/
simproc cycAssoc (((_ : UInt64) + _) + _) := fun e => do
  unless e.isAppOfArity ``HAdd.hAdd 6 do return .continue
  let xi := e.appFn!.appArg!
  unless xi.isAppOfArity ``HAdd.hAdd 6 do return .continue
  unless (← isInc xi.appArg!) && (← isInc e.appArg!) do return .continue
  rewriteWith ``u64_add_assoc #[xi.appFn!.appArg!, xi.appArg!, e.appArg!]

simproc cycCondAdd ((cond _ (_ : UInt64) _) + _) := fun e => do
  unless e.isAppOfArity ``HAdd.hAdd 6 do return .continue
  let some _ ← u64? e.appArg! | return .continue
  let c := e.appFn!.appArg!
  unless (← isCondLit c) do return .continue
  rewriteWith ``u64_cond_add #[c.getArg! 1, c.getArg! 2, c.getArg! 3, e.appArg!]

simproc cycAddCond ((_ : UInt64) + cond _ _ _) := fun e => do
  unless e.isAppOfArity ``HAdd.hAdd 6 do return .continue
  let some _ ← u64? e.appFn!.appArg! | return .continue
  let c := e.appArg!
  unless (← isCondLit c) do return .continue
  rewriteWith ``u64_add_cond #[c.getArg! 1, c.getArg! 2, c.getArg! 3, e.appFn!.appArg!]

/-- `cond c t t = t` when the branches are *syntactically* equal. `Bool.cond_self` as a
simp lemma would check every `bif` in the state by unification. -/
simproc condSame (cond _ _ _) := fun e => do
  unless e.isAppOfArity ``cond 4 do return .continue
  let t := e.getArg! 2
  unless t == e.getArg! 3 do return .continue
  let .const _ us := e.getAppFn | return .continue
  return .done { expr := t, proof? := some (mkApp3 (mkConst ``Bool.cond_self us) (e.getArg! 0) (e.getArg! 1) t) }

end Smb.Simprocs
