import Smb.Plain
import Smb.Run
import Smb.Simprocs
import Std.Tactic.BVDecide

/-!
# Symbolic execution on the plain machine

`sym_exec` rewrites `(prog).run s` forwards from the state: each bind runs its first
part on the current state, so instruction fetches see a concrete PC and (via code
hypotheses) a concrete opcode. `CPU.exec` is unfolded only once its opcode is a literal,
so no opcode is ever expanded symbolically. A branch on symbolic data turns the state
into an `if`; `run_ite_state` then executes both paths separately.

The result is a term over the initial symbolic registers and memory, which `bv_decide`
can check (or refute with a concrete counterexample).
-/
namespace Smb.Symbolic
open Lean Meta Simp Smb.Simprocs

variable {σ α β : Type}

theorem run_bind (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl
theorem run_pure (a : α) (s : σ) : (pure a : StateM σ α).run s = (a, s) := rfl
/-! Control flow. Bool-conditioned `if`s become `cond` before their conditions are
simplified (`↓ite_bool`): an `if` carries a `Decidable` instance that would keep mentioning
the condition's old form after rewriting, which stops later lemmas from matching. -/

theorem ite_bool {b : Bool} {inst : Decidable (b = true)} (x y : α) :
    @ite α (b = true) inst x y = cond b x y := by
  cases b <;> cases inst <;> simp_all
-- `StateT.run` returns `Id (α × σ)`; the results below are typed at `α × σ` so that the
-- `Prod` projection lemmas match them.
theorem run_cond (b : Bool) (x y : StateM σ α) (s : σ) :
    (cond b x y).run s = @cond (α × σ) b (x.run s) (y.run s) := by cases b <;> rfl
theorem run_cond_state (m : StateM σ α) (b : Bool) (s₁ s₂ : σ) :
    m.run (cond b s₁ s₂) = @cond (α × σ) b (m.run s₁) (m.run s₂) := by cases b <;> rfl
theorem fst_cond (b : Bool) (p q : α × β) : (cond b p q).1 = cond b p.1 q.1 := by cases b <;> rfl
theorem snd_cond (b : Bool) (p q : α × β) : (cond b p q).2 = cond b p.2 q.2 := by cases b <;> rfl
theorem app_cond {γ : Type} (b : Bool) (f g : γ → α) (i : γ) : (cond b f g) i = cond b (f i) (g i) := by
  cases b <;> rfl
theorem run_ite {c : Prop} {inst : Decidable c} (a b : StateM σ α) (s : σ) :
    (@ite _ c inst a b).run s = @ite (α × σ) c inst (a.run s) (b.run s) := by cases inst <;> rfl

/-! Projections of a branched state. -/
theorem Plain.regs_cond (b : Bool) (s t : Plain) : (cond b s t).regs = cond b s.regs t.regs := by cases b <;> rfl
theorem Plain.ram_cond (b : Bool) (s t : Plain) : (cond b s t).ram = cond b s.ram t.ram := by cases b <;> rfl
theorem Plain.cyc_cond (b : Bool) (s t : Plain) : (cond b s t).cyc = cond b s.cyc t.cyc := by cases b <;> rfl
theorem Plain.bad_cond (b : Bool) (s t : Plain) : (cond b s t).bad = cond b s.bad t.bad := by cases b <;> rfl
theorem Regs.pc_cond (b : Bool) (r q : Regs) : (cond b r q).pc = cond b r.pc q.pc := by cases b <;> rfl
theorem Regs.a_cond (b : Bool) (r q : Regs) : (cond b r q).a = cond b r.a q.a := by cases b <;> rfl
theorem Regs.x_cond (b : Bool) (r q : Regs) : (cond b r q).x = cond b r.x q.x := by cases b <;> rfl
theorem Regs.y_cond (b : Bool) (r q : Regs) : (cond b r q).y = cond b r.y q.y := by cases b <;> rfl
theorem Regs.s_cond (b : Bool) (r q : Regs) : (cond b r q).s = cond b r.s q.s := by cases b <;> rfl
theorem Regs.p_cond (b : Bool) (r q : Regs) : (cond b r q).p = cond b r.p q.p := by cases b <;> rfl

section Plain
variable (s : Plain)
theorem getRegs_run : (CPU.getRegs (σ := Plain)).run s = (s.regs, s) := rfl
theorem modRegs_run (f : Regs → Regs) : (CPU.modRegs (σ := Plain) f).run s = ((), { s with regs := f s.regs }) := rfl
theorem rd_run (a : UInt16) : (CPU.rd (σ := Plain) a).run s = Plain.read s a := rfl
theorem wr_run (a : UInt16) (b : UInt8) : (CPU.wr (σ := Plain) a b).run s = ((), Plain.write s a b) := rfl
theorem idle_run : (CPU.idle (σ := Plain)).run s = ((), { s with cyc := s.cyc + 1 }) := rfl
theorem unsupported_run : (CPU.unsupported (σ := Plain)).run s = ((), { s with bad := true }) := rfl
theorem nmiPending_run : (CPU.nmiPending (σ := Plain)).run s = (false, s) := rfl
theorem clearNmiPending_run : (CPU.clearNmiPending (σ := Plain)).run s = ((), s) := rfl
theorem nmiPolled_run : (CPU.nmiPolled (σ := Plain)).run s = (false, s) := rfl
theorem setNmiPolled_run (b : Bool) : (CPU.setNmiPolled (σ := Plain) b).run s = ((), s) := rfl

/-! Address ranges. Accesses never branch on them; these only tidy the `bad` flag and the
choice between RAM and ROM in `memRead` when the range is evident from the address's form.
Anything else stays a Boolean term for the final `bv_decide`. -/
theorem zp_inRam (b : UInt8) : decide (b.toUInt16 < 0x2000) = true := by
  simp only [decide_eq_true_eq]; bv_decide
theorem stack_inRam (b : UInt8) : decide ((256 ||| b.toUInt16) < 0x2000) = true := by
  simp only [decide_eq_true_eq]; bv_decide
theorem add_inRam (c : UInt16) (b : UInt8) (h : c ≤ 0x1F00) : decide (c + b.toUInt16 < 0x2000) = true := by
  simp only [decide_eq_true_eq]; bv_decide
/-- The page-crossing dummy read of `abs,X`/`abs,Y`: the base's page, the indexed low byte. -/
theorem page_inRam (c y : UInt16) (h : c ≤ 0x1F00) : decide ((c ||| (y &&& 255)) < 0x2000) = true := by
  simp only [decide_eq_true_eq]; bv_decide

/-! Memory regions. A stack cell (`$100 | b`) is never a literal address outside `$100–$1FF`,
nor a zero-page-indexed cell; a zero-page-indexed cell (`(c + x) mod 256`) is never a literal
`≥ $100`. These decide read-after-write questions that would otherwise stay as `bif`s, e.g.
an RTS reading its return address through a called routine's closed-form RAM. -/
theorem lit_ne_stack (c : UInt16) (b : UInt8) (h : (c < 256 || 512 ≤ c) = true) :
    (c == (256 ||| b.toUInt16) &&& 2047) = false := by
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h; bv_decide
theorem stack_ne_lit (c : UInt16) (b : UInt8) (h : (c < 256 || 512 ≤ c) = true) :
    ((256 ||| b.toUInt16) &&& 2047 == c) = false := by
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h; bv_decide
theorem zpx_ne_stack (c x b : UInt8) : ((c + x).toUInt16 &&& 2047 == (256 ||| b.toUInt16) &&& 2047) = false := by
  bv_decide
theorem stack_ne_zpx (c x b : UInt8) : ((256 ||| b.toUInt16) &&& 2047 == (c + x).toUInt16 &&& 2047) = false := by
  bv_decide
theorem lit_ne_zpx (n : UInt16) (c x : UInt8) (h : (256 ≤ n) = true) :
    (n == (c + x).toUInt16 &&& 2047) = false := by
  bv_decide
theorem zpx_ne_lit (n : UInt16) (c x : UInt8) (h : (256 ≤ n) = true) :
    ((c + x).toUInt16 &&& 2047 == n) = false := by
  bv_decide

/-- Different offsets from the same stack pointer are different stack cells. -/
theorem stack_ne_off (b k₁ k₂ : UInt8) (h : (k₁ != k₂) = true) :
    ((256 ||| (b + k₁).toUInt16) &&& 2047 == (256 ||| (b + k₂).toUInt16) &&& 2047) = false := by
  simp only [bne_iff_ne, ne_eq] at h; bv_decide
theorem stack_ne_off_l (b k : UInt8) (h : (k != 0) = true) :
    ((256 ||| (b + k).toUInt16) &&& 2047 == (256 ||| b.toUInt16) &&& 2047) = false := by
  simp only [bne_iff_ne, ne_eq] at h; bv_decide
theorem stack_ne_off_r (b k : UInt8) (h : (k != 0) = true) :
    ((256 ||| b.toUInt16) &&& 2047 == (256 ||| (b + k).toUInt16) &&& 2047) = false := by
  simp only [bne_iff_ne, ne_eq] at h; bv_decide

/-- A conditional dummy read only costs a cycle (and must be in range). -/
theorem dummyRdIf_run (c : Bool) (a : UInt16) :
    (CPU.dummyRdIf (σ := Plain) c a).run s =
      ((), { s with cyc := s.cyc + cond c 1 0, bad := s.bad || (c && !Plain.readable a) }) := by
  cases c
  · show ((), s) = ((), { s with cyc := s.cyc + 0, bad := s.bad || false })
    simp
  · rfl

/-- The post-instruction IRQ check folds into `bad` instead of splitting the path. -/
theorem cond_unsupported (c : Bool) (r : Regs) (m g : UInt16 → UInt8) (k : UInt64) (b : Bool) :
    @cond (Unit × Plain) c ((), ⟨r, m, g, k, true⟩) ((), ⟨r, m, g, k, b⟩) = ((), ⟨r, m, g, k, b || c⟩) := by
  cases c <;> cases b <;> rfl

/-- `runTo`, only in applied form, so its later iterations are never unfolded as program text. -/
theorem runTo_run_zero (stop : UInt16) : (CPU.runTo (σ := Plain) stop 0).run s = ((), s) := rfl
theorem runTo_run_succ (stop : UInt16) (n : Nat) :
    (CPU.runTo (σ := Plain) stop (n + 1)).run s =
      if s.regs.pc = stop then ((), s) else (CPU.runTo stop n).run (CPU.step.run s).2 := by
  by_cases h : s.regs.pc = stop
  · simp only [h, ↓reduceIte]; simp [CPU.runTo, CPU.getRegs, StateT.run, bind, StateT.bind, h, Bus.regs]; rfl
  · simp only [h, ↓reduceIte]; simp [CPU.runTo, CPU.getRegs, StateT.run, bind, StateT.bind, h, Bus.regs]; rfl

theorem runTo_snd_step (stop : UInt16) (n : Nat) (h : s.regs.pc ≠ stop) :
    ((CPU.runTo (σ := Plain) stop (n + 1)).run s).2 = ((CPU.runTo stop n).run (CPU.step.run s).2).2 := by
  rw [runTo_run_succ]; simp [h]
theorem runTo_snd_stop (stop : UInt16) (n : Nat) (h : s.regs.pc = stop) :
    ((CPU.runTo (σ := Plain) stop (n + 1)).run s).2 = s := by
  rw [runTo_run_succ]; simp [h]

end Plain

/-- Unfold `CPU.exec op` only when `op` is a literal. -/
dsimproc execLit (CPU.exec _) := fun e => do
  unless e.isAppOfArity ``CPU.exec 3 do return .continue
  let some _ ← u8? e.appArg! | return .continue
  let some e' ← delta? e (· == ``CPU.exec) | return .continue
  return .visit e'.headBeta

/-- Present a literal fuel `n + 1` to `CPU.runTo` so its equation lemmas apply. -/
dsimproc runToLit (CPU.runTo _ _) := fun e => do
  unless e.isAppOfArity ``CPU.runTo 4 do return .continue
  let some n ← Nat.fromExpr? e.appArg! | return .continue
  if n == 0 then return .continue
  return .visit (mkApp e.appFn! (mkNatAdd (mkNatLit (n - 1)) (mkNatLit 1)))

/-- `decide`, but only on goals without free variables. On a goal over symbolic values,
`decide` evaluates the `Decidable` instance by unfolding bit arithmetic until it gets stuck,
which is costly and can never succeed. -/
elab "decide_closed" : tactic => do
  if (← instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).hasFVar then
    throwError "decide_closed: goal has free variables"
  Lean.Elab.Tactic.evalTactic (← `(tactic| decide))

/-- Symbolic execution of plain-machine CPU code. Extra simp lemmas (code bytes, facts
about the initial state) are passed in brackets. -/
syntax "sym_exec" ("[" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| sym_exec $[$loc]?) => `(tactic| sym_exec [] $[$loc]?)
  | `(tactic| sym_exec [$extra,*] $[$loc]?) => `(tactic|
      simp (config := {decide := false, maxSteps := 10000000}) (disch := decide_closed) only [
        ↓ite_bool, run_bind, run_pure, run_cond, run_cond_state, fst_cond, snd_cond, app_cond, run_ite,
        Plain.regs_cond, Plain.ram_cond, Plain.cyc_cond, Plain.bad_cond, Regs.pc_cond, Regs.a_cond,
        Regs.x_cond, Regs.y_cond, Regs.s_cond, Regs.p_cond, Bool.cond_true, Bool.cond_false,
        Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_true, Bool.true_or,
        Bool.not_true,
        getRegs_run, modRegs_run, rd_run, wr_run, idle_run, unsupported_run, nmiPending_run,
        clearNmiPending_run, nmiPolled_run, setNmiPolled_run,
        execLit, runToLit, runTo_run_zero, runTo_run_succ, CPU.step,
        CPU.setNZ, CPU.flag, CPU.setA, CPU.setX, CPU.setY, CPU.fetch, CPU.fetch16, CPU.dummyPc,
        CPU.dummyStack, CPU.push, CPU.pull, CPU.aZp, CPU.aZpX, CPU.aZpY, CPU.aAbs, CPU.aAbsI,
        CPU.aAbsX, CPU.aAbsY, CPU.aIndX, CPU.aIndY, CPU.adc, CPU.cmp, CPU.branch, CPU.shiftOp,
        CPU.rmw, CPU.interrupt, CPU.nmi, CPU.ld, CPU.st, CPU.aluOperand, CPU.isAlu, CPU.alu,
        Plain.read, Plain.write, Plain.memRead, Plain.inRam, Plain.readable, zp_inRam, stack_inRam,
        add_inRam, page_inRam, lit_ne_stack, stack_ne_lit, zpx_ne_stack, stack_ne_zpx,
        lit_ne_zpx, zpx_ne_lit, stack_ne_off, stack_ne_off_l, stack_ne_off_r, dummyRdIf_run, cond_unsupported, decide_true, decide_false, Bool.not_false, Bool.or_self,
        Bool.true_or, Bool.or_true, beq_self_eq_true,
        CPU.FC, CPU.FZ, CPU.FI, CPU.FD, CPU.FB, CPU.FU, CPU.FV, CPU.FN,
        UInt16.reduceAdd, UInt16.reduceSub, UInt16.reduceLT, UInt16.reduceLE, UInt16.reduceGE,
        UInt16.reduceGT, UInt8.reduceAdd, UInt8.reduceSub, UInt64.reduceAdd,
        u8and, u8or, u8xor, u8shl, u8shr, u16and, u16or, u16xor, u16shl, u16shr,
        u8beq, u8bne, u16beq, u16bne, u8eq, u16eq, u8not, u8toU16, u16toU8,
        ↓reduceIte, ite_self, Bool.false_eq_true, Bool.or_false, Bool.false_or, Bool.not_false,
        iteLit, iteFlag, condFlag, maskOr, maskAnd, maskCond, shr7Mask, condBeq, condBne, condToU16, condSame, cycAssoc, cycCondAdd,
        cycAddCond, u8_and_zero, u8_or_zero, u8_zero_or, cond_true_false', cond_false_true',
        UInt64.add_zero, UInt8.add_zero, UInt8.sub_zero, UInt16.add_zero, UInt8.sub_add_cancel, UInt8.add_sub_cancel, u8SubLit, u8AddLit,
        $extra,*] $[$loc]?)

end Smb.Symbolic
