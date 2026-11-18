import Smb.Goal.StartRun
import Smb.Routine.ModelStep
import Smb.Routine.HorizontalLimitNes

/-!
# The frame contract

`Follows` asks a whole frame to act like the model. `Smb.Routine.ModelFrame` has proved that of `PlayerCtrlRoutine`, for a frame that touches only the floor. `PlayerFrame` is what's left: the rest of the frame.

So what remains of `Follows` on open ground is `PlayerFrame` and the frame's conditions, and `follows_of_contract` proves `Follows` from them. None of what `PlayerFrame` says is proved yet.
-/
namespace Smb.Goal.OneOne

open Smb.Movement
open Smb.Routine (ramAt)
open Smb.Routine.HorizontalLimit (pixelP leftL phi pack)
open Smb.Routine.ModelBridge (cellsOf inOfRam modelMove)
open Smb.Routine.ModelFrame
open Smb.Routine.ModelStep
open Smb.Routine (romFn)
open Smb.Routine (sext)

/-- The bytes the model describes, read through `ramAt`. -/
theorem stateOf_eq (s : NES) : stateOf s = cellsOf (ramAt s) := rfl

/-- What the frame does around `PlayerCtrlRoutine`. Control reaches its entry once, in state `s`, with the model's cells as the last frame left them, apart from `$783`, which the model takes as an input. It leaves them as the routine does, but for `$0D`, which `SaveAB` takes from the buttons. -/
structure PlayerFrame (inputs : List UInt8) (f : Nat) (s : NES) (m : Nat) : Prop where
  quiet : s.Quiet
  prg : s.prg = Smb.prg
  pc : s.pc = 0xB0E9
  iflag : (s.p &&& 4 == 0) = false
  entry : cellsOf (ramAt s) = { stateOf (at' inputs f) with t783 := ramAt s 0x783 }
  page : ramAt s 0x6D = ramAt (at' inputs f) 0x6D
  pixel : ramAt s 0x86 = ramAt (at' inputs f) 0x86
  frac : ramAt s 0x400 = ramAt (at' inputs f) 0x400
  left1 : ramAt s 0x71A = ramAt (at' inputs f) 0x71A
  left2 : ramAt s 0x71C = ramAt (at' inputs f) 0x71C
  out57 : ramAt (at' inputs (f + 1)) 0x57 = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x57
  out705 : ramAt (at' inputs (f + 1)) 0x705 = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x705
  out700 : ramAt (at' inputs (f + 1)) 0x700 = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x700
  out33 : ramAt (at' inputs (f + 1)) 0x33 = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x33
  out45 : ramAt (at' inputs (f + 1)) 0x45 = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x45
  out1d : ramAt (at' inputs (f + 1)) 0x1D = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x1D
  out783 : ramAt (at' inputs (f + 1)) 0x783 = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x783
  out703 : ramAt (at' inputs (f + 1)) 0x703 = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x703
  outce : ramAt (at' inputs (f + 1)) 0xCE = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0xCE
  out416 : ramAt (at' inputs (f + 1)) 0x416 = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x416
  out9f : ramAt (at' inputs (f + 1)) 0x9F = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x9F
  out433 : ramAt (at' inputs (f + 1)) 0x433 = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x433
  out709 : ramAt (at' inputs (f + 1)) 0x709 = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x709
  out70a : ramAt (at' inputs (f + 1)) 0x70A = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x70A
  out708 : ramAt (at' inputs (f + 1)) 0x708 = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x708
  out706 : ramAt (at' inputs (f + 1)) 0x706 = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x706
  outPage : ramAt (at' inputs (f + 1)) 0x6D = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x6D
  outPixel : ramAt (at' inputs (f + 1)) 0x86 = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x86
  outFrac : ramAt (at' inputs (f + 1)) 0x400 = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 0x400
  saveAB : byte (at' inputs (f + 1)) 0x0D &&& 0x80 = ramAt s 0x6FC &&& 0x80
  onScreen : pixelP (ramAt (at' inputs (f + 1))) - leftL (ramAt (at' inputs (f + 1))) < 0x8000

theorem setMove_v (M : S) : (setMove M).v = M.v := Smb.Movement.setMove_v M

/-- A frame that doesn't run the player, as a paused one, leaves the model's cells and the position alone. -/
structure StillFrame (inputs : List UInt8) (f : Nat) : Prop where
  same : view openGround (at' inputs (f + 1)) = view openGround (at' inputs f)
  posSame : pos (at' inputs (f + 1)) = pos (at' inputs f)

theorem follows_of_still {inputs : List UInt8} {i f : Nat} (h : StillFrame inputs f) : Follows openGround inputs i f :=
  ⟨.still, trivial, h.same, by simp [delta, h.posSame]⟩

/-- The position after a speed, as numbers. -/
theorem pos_step (x : UInt32) (v : UInt8) (hlo : 0x800 ≤ x) (hhi : x < 0x800000) :
    (((x + sext v * 16) &&& 0xFFFFFF).toNat : Int) = x.toNat + signed v * 16 := by
  have hv := v.toNat_lt
  have hlo' : 0x800 ≤ x.toNat := hlo
  have hhi' : x.toNat < 0x800000 := hhi
  by_cases h : v < 0x80
  · have h' : v.toNat < 128 := h
    have e : (x + sext v * 16) &&& 0xFFFFFF = x + v.toUInt32 * 16 := by
      simp only [sext, h, decide_true, cond_true]
      revert hhi h
      bv_decide (config := { enums := false })
    rw [e]
    have h16 : (16 : UInt32).toNat = 16 := rfl
    simp only [signed, h, if_true, UInt32.toNat_add, UInt32.toNat_mul, UInt8.toNat_toUInt32, h16]
    omega
  · have h' : 128 ≤ v.toNat := by simpa [UInt8.lt_iff_toNat_lt] using h
    have e : ((x + sext v * 16) &&& 0xFFFFFF) + (0 - v).toUInt32 * 16 = x := by
      simp only [sext, h, decide_false, cond_false]
      revert hlo hhi h
      bv_decide (config := { enums := false })
    have e2 : (0 - v).toNat = 256 - v.toNat := by
      have : (0 - v).toNat = (256 - v.toNat) % 256 := by
        rw [UInt8.toNat_sub]; simp
      omega
    have hn := congrArg UInt32.toNat e
    have h16 : (16 : UInt32).toNat = 16 := rfl
    simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt8.toNat_toUInt32, e2, h16] at hn
    simp only [signed, h, if_false]
    have hrb : ((x + sext v * 16) &&& 0xFFFFFF) ≤ 0xFFFFFF := by bv_decide (config := { enums := false })
    have hrb' : ((x + sext v * 16) &&& 0xFFFFFF).toNat ≤ 0xFFFFFF := hrb
    generalize ((x + sext v * 16) &&& 0xFFFFFF).toNat = r at *
    omega

/-- What a frame's collision has to be, on open ground: all that `PlayerBGCollision` reads comes out clear. -/
structure OpenBg (sp : UInt8) (R : UInt16 → UInt8) : Prop where
  go : Smb.Routine.bgPre_pc R = 0xDC98
  head : Smb.Routine.headBlocked romFn (Smb.Routine.bgRam R) (Smb.Routine.bgY R) = false
  headc : Smb.Routine.headCoin romFn (Smb.Routine.bgRam R) (Smb.Routine.bgY R) = false
  headh : Smb.Routine.headHit romFn (Smb.Routine.bgRam R) (Smb.Routine.bgY R) = false
  coin : Smb.Routine.footCoin romFn (Smb.Routine.bgRam R) (Smb.Routine.bgY R) = false
  axe : Smb.Routine.footAxeAt romFn (Smb.Routine.bgRam R) (Smb.Routine.bgY R) = false
  pipe : Smb.Routine.pipeEntryAt romFn (Smb.Routine.bgRam R) (Smb.Routine.bgY R) = false
  imp : Smb.Routine.impeded romFn (Smb.Routine.bgRam R) (Smb.Routine.bgY R) = false
  foot : Smb.Routine.footCheck_pc (Smb.Routine.bgY R) (Smb.Routine.bgSize_s (Smb.Routine.bgPre_s sp)) (Smb.Routine.bgRam R) romFn = 0xDD5E
  eb : Smb.Routine.bgFootRam sp romFn R 0xEB < 0x16
  spring : (Smb.Routine.footTile romFn (Smb.Routine.bgRam R) (Smb.Routine.bgY R) != 0x67 && Smb.Routine.footTile romFn (Smb.Routine.bgRam R) (Smb.Routine.bgY R) != 0x68) = true
  noCoin : Smb.Routine.noSideCoin romFn (Smb.Routine.bgFootRam sp romFn R) = true
  noClimb : Smb.Routine.noSideClimb romFn (Smb.Routine.bgFootRam sp romFn R) = true
  noPipe : Smb.Routine.noSidePipeEntry romFn (Smb.Routine.bgFootRam sp romFn R) = true
  side : Smb.Routine.sideBlocks romFn (Smb.Routine.bgFootRam sp romFn R) = false
  js : R 0x70E = 0
  swim : R 0x704 = 0
  st : R 0x1D ≤ 2

/-- `$0D`'s A bit as the model's. -/
theorem prevA_of_pad (b : UInt8) : b &&& 0x80 = if (b &&& 0x80 != 0) = true then 0x80 else 0 := by
  by_cases h : (b &&& 0x80 != 0) = true
  · simp only [h, if_true]
    simp only [bne] at h
    revert h
    bv_decide (config := { enums := false })
  · simp only [h, if_false]
    simp only [bne] at h
    revert h
    bv_decide (config := { enums := false })

theorem OpenBg.clear {sp : UInt8} {R : UInt16 → UInt8} (h : OpenBg sp R) (w : UInt16 → UInt8) : BgClear w sp R romFn :=
  ⟨h.go, h.head, h.headc, h.coin, h.axe, h.pipe, h.imp, h.spring, h.side, h.js, h.swim, h.st⟩

/-- The frame's end, from what the routine leaves. -/
theorem state_of_parts {inputs : List UInt8} {f : Nat} {s : NES} {m : Nat} (hc : PlayerFrame inputs f s m) (F : UInt16 → UInt8) (X : S)
    (he : ∀ a : UInt16, a < 0x800 → ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 a = F a) (hmodel : cellsOf F = X) :
    stateOf (at' inputs (f + 1)) = { X with prevA := if (inOfRam (ramAt s)).a then 0x80 else 0 } := by
  refine S_ext
    ((hc.out57.trans (he 0x57 (by decide))).trans (congrArg S.v hmodel))
    ((hc.out705.trans (he 0x705 (by decide))).trans (congrArg S.f hmodel))
    ((hc.out700.trans (he 0x700 (by decide))).trans (congrArg S.abs hmodel))
    ((hc.out33.trans (he 0x33 (by decide))).trans (congrArg S.face hmodel))
    ((hc.out45.trans (he 0x45 (by decide))).trans (congrArg S.move hmodel))
    ((hc.out1d.trans (he 0x1D (by decide))).trans (congrArg S.st hmodel))
    ((hc.out783.trans (he 0x783 (by decide))).trans (congrArg S.t783 hmodel))
    ((hc.out703.trans (he 0x703 (by decide))).trans (congrArg S.r703 hmodel))
    ((hc.outce.trans (he 0xCE (by decide))).trans (congrArg S.y hmodel))
    ((hc.out416.trans (he 0x416 (by decide))).trans (congrArg S.ysub hmodel))
    ((hc.out9f.trans (he 0x9F (by decide))).trans (congrArg S.vy hmodel))
    ((hc.out433.trans (he 0x433 (by decide))).trans (congrArg S.vf hmodel))
    ((hc.out709.trans (he 0x709 (by decide))).trans (congrArg S.g hmodel))
    ((hc.out70a.trans (he 0x70A (by decide))).trans (congrArg S.gfall hmodel))
    ((hc.out708.trans (he 0x708 (by decide))).trans (congrArg S.y0 hmodel))
    ((hc.out706.trans (he 0x706 (by decide))).trans (congrArg S.rise hmodel))
    ?_
  show byte (at' inputs (f + 1)) 0x0D &&& 0x80 = if (ramAt s 0x6FC &&& 0x80 != 0) = true then 0x80 else 0
  rw [hc.saveAB]
  exact prevA_of_pad _

set_option maxHeartbeats 2000000 in
/-- The routine's end state, carried by the contract to the frame's end, is a step of the model. -/
theorem follows_of_parts {inputs : List UInt8} {i f : Nat} {s : NES} {m : Nat} (hc : PlayerFrame inputs f s m) (F : UInt16 → UInt8) (L : Bool)
    (he : ∀ a : UInt16, a < 0x800 → ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 a = F a)
    (hmodel : cellsOf F = afterBg L (setMove (modelMove (ramAt s))))
    (hpos : pack (pixelP F) (F 0x400) = (pack (pixelP (ramAt s)) (ramAt s 0x400) + sext (modelMove (ramAt s)).v * 16) &&& 0xFFFFFF)
    (hspd : ramAt s 0x9F + 0x40 < 0x80) (hA : Away (ramAt s))
    (hy : (stateOf (at' inputs f)).st = 0 → (stateOf (at' inputs f)).y &&& 0xF0 = (stateOf (at' inputs f)).y)
    (hw : 8 ≤ pixelP (ramAt s) ∧ pixelP (ramAt s) < 0x8000)
    (hl : L = ((modelMove (ramAt s)).st == 0 || landC 176 (modelMove (ramAt s)))) :
    Follows openGround inputs i f := by
  have hi0 : cellsOf (ramAt s) = { stateOf (at' inputs f) with t783 := ramAt s 0x783 } := hc.entry
  have hM : modelMove (ramAt s) = fallS (moved (inOfRam (ramAt s)) (cellsOf (ramAt s))) := rfl
  have hvw : norm openGround (cellsOf (ramAt s)) = norm openGround (stateOf (at' inputs f)) := by
    rw [hi0]
    generalize stateOf (at' inputs f) = q
    unfold norm
    repeat' split
    all_goals simp_all
  rw [hM] at hmodel hl hpos
  generalize hX : afterBg L (setMove (fallS (moved (inOfRam (ramAt s)) (cellsOf (ramAt s))))) = X at hmodel
  have hstate := state_of_parts hc F X he hmodel
  have hst0 : (cellsOf (ramAt s)).st = (stateOf (at' inputs f)).st := by rw [hi0]
  have hy0 : (cellsOf (ramAt s)).y = (stateOf (at' inputs f)).y := by rw [hi0]
  have hstep := step_of_bg (inOfRam (ramAt s)) (cellsOf (ramAt s)) L hspd (by rw [hst0, hy0]; exact hy) hl
  rw [hvw] at hstep
  subst hX
  rw [← hstate] at hstep
  refine ⟨.go 176 false (effIn (cellsOf (ramAt s)) (inOfRam (ramAt s))), ⟨Or.inl rfl, by simp⟩, by simp only [view, nextS]; exact hstep, ?_⟩
  have hvel : (step openGround 176 false (effIn (cellsOf (ramAt s)) (inOfRam (ramAt s))) (norm openGround (stateOf (at' inputs f)))).v = (fallS (moved (inOfRam (ramAt s)) (cellsOf (ramAt s)))).v := by
    rw [← hstep, norm_v, hstate]
    show (afterBg L _).v = _
    have h1 : ∀ (M : S), (afterBg L M).v = M.v := by
      intro M
      unfold afterBg
      repeat' split
      all_goals rfl
    rw [h1, setMove_v]
  have hrel : pixelP (ramAt (at' inputs f)) - leftL (ramAt (at' inputs f)) = pixelP (ramAt s) - leftL (ramAt s) := by
    simp only [pixelP, leftL, hc.page, hc.pixel, hc.left1, hc.left2]
  have hphi0 : phi (ramAt (at' inputs f)) = pack (pixelP (ramAt s)) (ramAt s 0x400) := by
    have hlt : pixelP (ramAt (at' inputs f)) - leftL (ramAt (at' inputs f)) < 0x8000 := by
      rw [hrel]
      have hf := hA.far
      generalize pixelP (ramAt s) - leftL (ramAt s) = d at *
      bv_decide (config := { enums := false })
    simp only [phi, hlt, decide_true, Bool.cond_true]
    simp only [pixelP, hc.page, hc.pixel, hc.frac]
  have hphi1 : phi (ramAt (at' inputs (f + 1))) = pack (pixelP F) (F 0x400) := by
    simp only [phi, hc.onScreen, decide_true, Bool.cond_true]
    simp only [pixelP, hc.outPage, hc.outPixel, hc.outFrac, he 0x6D (by decide), he 0x86 (by decide), he 0x400 (by decide)]
  have hbound : (0x800 : UInt32) ≤ pack (pixelP (ramAt s)) (ramAt s 0x400) ∧ pack (pixelP (ramAt s)) (ramAt s 0x400) < 0x800000 := by
    obtain ⟨h1, h2⟩ := hw
    simp only [pack]
    generalize pixelP (ramAt s) = P at *
    generalize ramAt s 0x400 = q at *
    bv_decide (config := { enums := false })
  have hstepPos := pos_step _ (fallS (moved (inOfRam (ramAt s)) (cellsOf (ramAt s)))).v hbound.1 hbound.2
  rw [← hpos] at hstepPos
  simp only [pos, delta, adv, view, hphi0, hphi1, hvel]
  exact hstepPos

/-- State 0: the contract and clear collision give `Follows` on open ground. -/
theorem follows_of_contract0 {inputs : List UInt8} {i f : Nat} {s : NES} {m : Nat} (hc : PlayerFrame inputs f s m)
    (hm : Move0Hyps (ramAt s)) (hA : Away (ramAt s)) (hv : Smb.Routine.HorizontalLimit.speedOk (ramAt s 0x57) = true)
    (hy : (stateOf (at' inputs f)).st = 0 → (stateOf (at' inputs f)).y &&& 0xF0 = (stateOf (at' inputs f)).y)
    (hb : OpenBg (Smb.Routine.frameS0 s.s) (Smb.Routine.frameR0 s.s (ramAt s) romFn))
    (hw : 8 ≤ pixelP (ramAt s) ∧ pixelP (ramAt s) < 0x8000)
    (hl : Smb.Routine.lands romFn (Smb.Routine.bgRam (Smb.Routine.frameR0 s.s (ramAt s) romFn)) (Smb.Routine.bgY (Smb.Routine.frameR0 s.s (ramAt s) romFn)) =
      ((modelMove (ramAt s)).st == 0 || landC 176 (modelMove (ramAt s)))) :
    Follows openGround inputs i f := by
  obtain ⟨p', a', x', y', c', w, hr, _⟩ := Smb.Routine.frame0_side_nes s hc.quiet hc.prg hc.pc m hc.iflag hm.ht hm.hz hm.hs hm.hjs hm.hspd hb.go hb.headc hb.headh hb.coin hb.axe hb.pipe hb.foot hb.eb hb.noCoin hb.noClimb hb.noPipe
  exact follows_of_parts hc (Smb.Routine.frame0_side_ram w s.s (ramAt s) romFn) _
    (fun a ha => by rw [Smb.Routine.ramAt_of_rel hr a, Smb.Routine.and7ff_of_lt a ha])
    (frame0_model w s.s (ramAt s) romFn hm hA hv Smb.Routine.HorizontalLimitNes.rom_climbTable (hb.clear w))
    (frame0_pos w s.s (ramAt s) romFn hm hA hv Smb.Routine.HorizontalLimitNes.rom_climbTable (hb.clear w))
    hm.hspd hA hy hw hl

/-- State 1: the contract and clear collision give `Follows` on open ground. -/
theorem follows_of_contract1 {inputs : List UInt8} {i f : Nat} {s : NES} {m : Nat} (hc : PlayerFrame inputs f s m)
    (hm : Move1Hyps (ramAt s)) (hA : Away (ramAt s)) (hv : Smb.Routine.HorizontalLimit.speedOk (ramAt s 0x57) = true)
    (hy : (stateOf (at' inputs f)).st = 0 → (stateOf (at' inputs f)).y &&& 0xF0 = (stateOf (at' inputs f)).y)
    (hb : OpenBg (Smb.Routine.frameS1 s.s) (Smb.Routine.frameR1 s.s (ramAt s) romFn))
    (hw : 8 ≤ pixelP (ramAt s) ∧ pixelP (ramAt s) < 0x8000)
    (hl : Smb.Routine.lands romFn (Smb.Routine.bgRam (Smb.Routine.frameR1 s.s (ramAt s) romFn)) (Smb.Routine.bgY (Smb.Routine.frameR1 s.s (ramAt s) romFn)) =
      ((modelMove (ramAt s)).st == 0 || landC 176 (modelMove (ramAt s)))) :
    Follows openGround inputs i f := by
  obtain ⟨p', a', x', y', c', w, hr, _⟩ := Smb.Routine.frame1_side_nes s hc.quiet hc.prg hc.pc m hc.iflag hm.ht hm.hz hm.hs hm.hjs hm.hspd hb.go hb.headc hb.headh hb.coin hb.axe hb.pipe hb.foot hb.eb hb.noCoin hb.noClimb hb.noPipe
  exact follows_of_parts hc (Smb.Routine.frame1_side_ram w s.s (ramAt s) romFn) _
    (fun a ha => by rw [Smb.Routine.ramAt_of_rel hr a, Smb.Routine.and7ff_of_lt a ha])
    (frame1_model w s.s (ramAt s) romFn hm hA hv Smb.Routine.HorizontalLimitNes.rom_climbTable (hb.clear w))
    (frame1_pos w s.s (ramAt s) romFn hm hA hv Smb.Routine.HorizontalLimitNes.rom_climbTable (hb.clear w))
    hm.hspd hA hy hw hl

/-- State 2: the contract and clear collision give `Follows` on open ground. -/
theorem follows_of_contract2 {inputs : List UInt8} {i f : Nat} {s : NES} {m : Nat} (hc : PlayerFrame inputs f s m)
    (hm : Move2Hyps (ramAt s)) (hA : Away (ramAt s)) (hv : Smb.Routine.HorizontalLimit.speedOk (ramAt s 0x57) = true)
    (hy : (stateOf (at' inputs f)).st = 0 → (stateOf (at' inputs f)).y &&& 0xF0 = (stateOf (at' inputs f)).y)
    (hb : OpenBg (Smb.Routine.frameS2 s.s) (Smb.Routine.frameR2 s.s (ramAt s) romFn))
    (hw : 8 ≤ pixelP (ramAt s) ∧ pixelP (ramAt s) < 0x8000)
    (hl : Smb.Routine.lands romFn (Smb.Routine.bgRam (Smb.Routine.frameR2 s.s (ramAt s) romFn)) (Smb.Routine.bgY (Smb.Routine.frameR2 s.s (ramAt s) romFn)) =
      ((modelMove (ramAt s)).st == 0 || landC 176 (modelMove (ramAt s)))) :
    Follows openGround inputs i f := by
  obtain ⟨p', a', x', y', c', w, hr, _⟩ := Smb.Routine.frame2_side_nes s hc.quiet hc.prg hc.pc m hc.iflag hm.ht hm.hz hm.hs hm.hjs hm.hspd hb.go hb.headc hb.headh hb.coin hb.axe hb.pipe hb.foot hb.eb hb.noCoin hb.noClimb hb.noPipe
  exact follows_of_parts hc (Smb.Routine.frame2_side_ram w s.s (ramAt s) romFn) _
    (fun a ha => by rw [Smb.Routine.ramAt_of_rel hr a, Smb.Routine.and7ff_of_lt a ha])
    (frame2_model w s.s (ramAt s) romFn hm hA hv Smb.Routine.HorizontalLimitNes.rom_climbTable (hb.clear w))
    (frame2_pos w s.s (ramAt s) romFn hm hA hv Smb.Routine.HorizontalLimitNes.rom_climbTable (hb.clear w))
    hm.hspd hA hy hw hl

end Smb.Goal.OneOne
