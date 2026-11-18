import Smb.Routine.FinishWritesNes
import Smb.Routine.NesBusStable
import Std.WP
import Std.Tactic.Do

/-!
# A full NES indirect-store tail cannot create finish

The selected $91 instruction tail includes its operand/address reads, store,
unsupported-I check and optional NMI entry. A has the filter range (zero or at
least $10) and RAM has 2 KiB; pointer, code, Quiet and support are unrestricted.
The opcode-byte fetch is still separate. This does not prove a legal entry history,
hardware equivalence, or that an indirect write cannot enable a later shortcut.

Small local Std.WP specifications compose push/interrupt/NMI using vcgen. They are
not registered globally, so unrelated proofs can choose their own bus properties.
-/

open Smb Std.WP Lean.Order
open Smb.Routine.FinishWritesNes
namespace Smb.Routine.NesStoreTail
set_option experimental.vcgen true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- Keep the full PPU/DMA bus implementation behind its proved interface.
attribute [local irreducible] NES.rdS NES.wrS

def NoFinish (s : NES) : Prop := s.ram.size = 0x800 ∧ finalVictory s ≠ true

theorem safe_of_ram_eq (s t : NES) (hr : t.ram = s.ram) (h : NoFinish s) : NoFinish t := by
  refine ⟨?_, ?_⟩
  · simpa only [hr] using h.1
  · intro hf
    rw [finish_eq_of_ram_eq s t hr] at hf
    exact h.2 hf

theorem filtered_write_safe (s : NES) (addr : UInt16) (v : UInt8)
    (h : NoFinish s) (hv : v = 0 ∨ 0x10 ≤ v) : NoFinish (NES.wrS s addr v) := by
  refine ⟨(write_preserves_ram_size s addr v).trans h.1, ?_⟩
  intro hf
  exact h.2 (filtered_write_cannot_create s addr v h.1 hv hf)

-- Stack stores may contain any byte, including 2/7/3, but cannot target finish RAM.
theorem stack_write_safe (s : NES) (sp v : UInt8) (h : NoFinish s) :
    NoFinish (NES.wrS s (0x100 ||| sp.toUInt16) v) := by
  let addr : UInt16 := 0x100 ||| sp.toUInt16
  let idx := (addr &&& 0x7FF).toNat
  have ha : addr < 0x2000 := by dsimp [addr]; bv_decide
  have hi : idx < 512 := by
    have hb : ((0x100 : UInt16) ||| sp.toUInt16) &&& 0x7FF < 512 := by bv_decide
    exact UInt16.lt_iff_toNat_lt.mp hb
  have hm : idx ≠ 0x770 := by omega
  have hw : idx ≠ 0x75F := by omega
  have hl : idx ≠ 0x75C := by omega
  have hr : (NES.wrS s addr v).ram = s.ram.set! idx v := by
    simp only [NES.BusRam.wrS_ram, ha, ↓reduceIte]
    rfl
  have hf : finalVictory (NES.wrS s addr v) = finalVictory s := by
    simp only [finalVictory, operMode, hr]
    rw [ByteArray.get!_set!_ne _ _ _ _ hm,
      ByteArray.get!_set!_ne _ _ _ _ hw, ByteArray.get!_set!_ne _ _ _ _ hl]
  refine ⟨(write_preserves_ram_size s addr v).trans h.1, ?_⟩
  intro hn
  rw [hf] at hn
  exact h.2 hn

theorem read_preserves_A (s : NES) (addr : UInt16) : (NES.rdS s addr).2.a = s.a :=
  congrArg Regs.a (NES.BusStable.rdS_regs s addr)

theorem fetch_frame (s : NES) :
    ((CPU.fetch (σ := NES)).run s).2.ram = s.ram ∧
    ((CPU.fetch (σ := NES)).run s).2.a = s.a := by
  change (NES.rdS {s with pc := s.pc + 1} s.pc).2.ram = s.ram ∧
    (NES.rdS {s with pc := s.pc + 1} s.pc).2.a = s.a
  exact ⟨NES.BusRam.rdS_ram _ _, read_preserves_A _ _⟩

theorem indy_frame (s : NES) :
    ((CPU.aIndY (σ := NES) true).run s).2.ram = s.ram ∧
    ((CPU.aIndY (σ := NES) true).run s).2.a = s.a := by
  let f := (CPU.fetch (σ := NES)).run s
  let l := NES.rdS f.2 f.1.toUInt16
  let h := NES.rdS l.2 (f.1 + 1).toUInt16
  let base := l.1.toUInt16 ||| (h.1.toUInt16 <<< 8)
  let addr := base + h.2.y.toUInt16
  let d := NES.rdS h.2 ((base &&& 0xFF00) ||| (addr &&& 0xFF))
  have he : ((CPU.aIndY (σ := NES) true).run s).2 = d.2 := rfl
  rw [he]
  have hf := fetch_frame s
  constructor
  · calc d.2.ram = h.2.ram := NES.BusRam.rdS_ram _ _
         _ = l.2.ram := NES.BusRam.rdS_ram _ _
         _ = f.2.ram := NES.BusRam.rdS_ram _ _
         _ = s.ram := hf.1
  · calc d.2.a = h.2.a := read_preserves_A _ _
         _ = l.2.a := read_preserves_A _ _
         _ = f.2.a := read_preserves_A _ _
         _ = s.a := hf.2

attribute [local irreducible] CPU.aIndY

theorem exec91_eq : CPU.exec (σ := NES) 0x91 = CPU.st (·.a) (CPU.aIndY true) := rfl

@[local spec] theorem exec91_safe :
    ⦃fun s => NoFinish s ∧ (s.a = 0 ∨ 0x10 ≤ s.a)⦄ CPU.exec (σ := NES) 0x91
    ⦃fun _ s => NoFinish s⦄ := by
  constructor
  intro s hs
  let q := (CPU.aIndY (σ := NES) true).run s
  have hq := indy_frame s
  rw [exec91_eq]
  change NoFinish (NES.wrS q.2 q.1 q.2.a)
  apply filtered_write_safe
  · exact safe_of_ram_eq s q.2 hq.1 hs.1
  · have hqa : q.2.a = s.a := hq.2
    rw [hqa]
    exact hs.2

-- Standard WP specifications forget read values/changed registers when only
-- RAM size and absence of finish matter. No PPU or DMA body is unfolded.
@[local spec] theorem rd_safe (addr : UInt16) :
    ⦃NoFinish⦄ CPU.rd (σ := NES) addr ⦃fun _ s => NoFinish s⦄ :=
  ⟨fun s h => safe_of_ram_eq s _ (NES.BusRam.rdS_ram s addr) h⟩

@[local spec] theorem getRegs_safe :
    ⦃NoFinish⦄ CPU.getRegs (σ := NES) ⦃fun _ s => NoFinish s⦄ := ⟨fun _ h => h⟩

@[local spec] theorem modRegs_safe (f : Regs → Regs) :
    ⦃NoFinish⦄ CPU.modRegs (σ := NES) f ⦃fun _ s => NoFinish s⦄ := ⟨fun _ h => h⟩

@[local spec] theorem wr_stack_safe (sp v : UInt8) :
    ⦃NoFinish⦄ CPU.wr (σ := NES) (0x100 ||| sp.toUInt16) v
    ⦃fun _ s => NoFinish s⦄ := ⟨fun s h => stack_write_safe s sp v h⟩

@[local spec] theorem unsupported_safe :
    ⦃NoFinish⦄ CPU.unsupported (σ := NES) ⦃fun _ s => NoFinish s⦄ := ⟨fun _ h => h⟩

@[local spec] theorem nmiPending_safe :
    ⦃NoFinish⦄ CPU.nmiPending (σ := NES) ⦃fun _ s => NoFinish s⦄ := ⟨fun _ h => h⟩

@[local spec] theorem clearNmiPending_safe :
    ⦃NoFinish⦄ CPU.clearNmiPending (σ := NES) ⦃fun _ s => NoFinish s⦄ := ⟨fun _ h => h⟩

@[local spec] theorem nmiPolled_safe :
    ⦃NoFinish⦄ CPU.nmiPolled (σ := NES) ⦃fun _ s => NoFinish s⦄ := ⟨fun _ h => h⟩

@[local spec] theorem push_safe (v : UInt8) :
    ⦃NoFinish⦄ CPU.push (σ := NES) v ⦃fun _ s => NoFinish s⦄ := by
  vcgen [CPU.push]
  all_goals assumption

@[local spec] theorem interrupt_safe (vec : UInt16) (brk : Bool) :
    ⦃NoFinish⦄ CPU.interrupt (σ := NES) vec brk ⦃fun _ s => NoFinish s⦄ := by
  vcgen [CPU.interrupt]
  all_goals assumption

@[local spec] theorem nmi_safe :
    ⦃NoFinish⦄ CPU.nmi (σ := NES) ⦃fun _ s => NoFinish s⦄ := by
  vcgen [CPU.nmi, CPU.dummyPc]
  all_goals assumption

theorem tail91_safe :
    ⦃fun s => NoFinish s ∧ (s.a = 0 ∨ 0x10 ≤ s.a)⦄ CPU.stepTail (σ := NES) 0x91
    ⦃fun _ s => NoFinish s⦄ := by
  vcgen [CPU.stepTail]
  all_goals assumption

theorem tail91_cannot_create (s : NES)
    (hs : s.ram.size = 0x800) (ha : s.a = 0 ∨ 0x10 ≤ s.a)
    (hf : finalVictory ((CPU.stepTail (σ := NES) 0x91).run s).2 = true) :
    finalVictory s = true := by
  by_cases h : finalVictory s = true
  · exact h
  · have ho := tail91_safe.le_wp s ⟨⟨hs,h⟩,ha⟩
    exact False.elim (ho.2 hf)

end Smb.Routine.NesStoreTail
