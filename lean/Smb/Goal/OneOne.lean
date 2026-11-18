import Smb.LocalBound.HorizontalDistance
import Smb.Routine.Launch
import Smb.Routine.AbsIO
import Smb.Tas

/-!
# The top-level 1-1 statement

An exit requires gameplay mode and a nonzero world or level byte. The mode
check excludes title-screen demos and the startup state, whose world and level
bytes are both `$FF`.

`ExitBound 1943`: no input leaves 1-1 in fewer than 1,943 frames, and none of those runs leaves the model. The TAS leaves on frame 1,943 exactly (`exitBound_tight`), so this
is the statement that the TAS's 1-1 can't be beaten. **It's a goal, not a theorem.**

`NoOverflow` imposes explicit limits on the two VRAM buffer offsets at each
instruction. `oneOne_of_deps` derives the bound under those limits if all the
fields of `Deps` hold. Those fields remain open.

| Field | Claim |
|---|---|
| `supported` | No such run of fewer than 1,943 frames sets `unmodelled` |
| `firstControl` | Leaving 1-1 means control started at frame 195 or later |
| `grabFirst` | From control, leaving 1-1 means grabbing the flag first |
| `covers` | For each `GrabKind`, up to a grab of that kind, each milestone goes on to one of `edges k`' successors, no sooner than the edge's weight |
| `flag` | A grab of kind `k` at `earliestGrab k` or later doesn't leave 1-1 before 1,943: 1,287 for a low grab, 1,260 for a high or skip grab |

A grab is high (`Y` ≤ 161), low (162–164) or in the walk-skip band (165–167, the full flagpole glitch). The kinds differ only in the last edge and in what follows the grab. The skip kind isn't assumed away: `flag .skip` asks only that a skip grab come too late to gain, which `flagSkip_of_noSkip` shows is weaker than asking that none happen.

Overflowing runs are outside this: `DirtyBound` is what the full goal would still need (`exitBound_of_cases`).

The weights are lower bounds for each stretch taken alone. A tight bound may need the milestones to carry more, such as timer phase, speed or sub-pixel, because the fastest version of each stretch need not fit together into one run.

The flag obligation relates the absolute grab and exit times. A later grab can
reach the same exit with a shorter wait for the next 21-tick timer boundary.
The TAS's low grab leads to a limiting count one tick beyond a boundary.
An earlier grab can also change the timer tally, so the time gain depends on
the resulting count. The low-grab edges on the TAS's path use its exact
observed times.

**Grab height decides the frame.** A high grab costs a slide of 61–62 frames and a walk of 92–103; a low one has no slide and a walk of 126. So a high grab can come earlier than the TAS's and still lose: `high_grab_witness` is a run that grabs 6 frames early at `Y` 138 and leaves a rule late. That run also shows pipe exit to grab takes under 240 frames, so the 240 can only be claimed for low grabs. High and skip grabs get a last edge of 213 and the earlier bound of 1,260, which is 27 frames looser.

`speedEdges` has the same graph with the weights the speed limit alone gives. `speedDist` shows those reach only frame 1,206, 81 short. `speed_edge` is how `HorizontalDistance` feeds that graph.
`launchEdges` adds the acceleration limit from `Launch`, for runs that start each stretch from rest, reaching frame 1,233, 54 short of a low grab's bound and 27 short of a high grab's. `launch_edge` feeds that one.
-/
namespace Smb.Goal
open Smb.Routine (ramAt)
open Smb.Routine.HorizontalLimit (phi XStep)
open Smb.LocalBound.HorizontalDistance
open Smb.Routine.Launch (LStep upSpeed gain launch_updates gain_pipe gain_bonus gain_flag)

/-- The state after the first `i` frames of `inputs`. `at' inputs (f + 1)` is the end of frame `f`. -/
def at' (inputs : List UInt8) (i : Nat) : NES := NES.runFrames (inputs.take i) initial

def byte (s : NES) (a : Nat) : UInt8 := s.ram.get! a
def engine (s : NES) : UInt8 := byte s 0x0E
def areaType (s : NES) : UInt8 := byte s 0x74E
def inGame (s : NES) : Bool := byte s 0x770 == 1
def pos (s : NES) : Nat := (phi (ramAt s)).toNat

/-- Gameplay is active and world or level has moved on. Both are zero-indexed.
The mode guard excludes power-on RAM and title-screen demo states. It does not
exclude corruption of these bytes during gameplay. -/
def left (s : NES) : Bool := inGame s && (byte s 0x75F != 0 || byte s 0x75C != 0)

/-- No run of fewer than `n` frames has left 1-1 or the model. -/
def ExitBound (n : Nat) : Prop :=
  ∀ inputs : List UInt8, inputs.length < n →
    let s := NES.runFrames inputs initial
    left s = false ∧ s.unmodelled = false

/-- The goal: frame 1,943 is the earliest. -/
def OneOneOptimal : Prop := ExitBound 1943

/-! ## The no-overflow assumption

A write past the 63 bytes of `VRAM_Buffer1` can reach `$0340` and
subsequent cells. `NoOverflow` bounds the two offsets at each instruction,
since an offset can rise and be reset within a frame.

The hypothesis bounds `$0340` by `$21` during normal play and by `$90` in
other phases. Area loads use the larger range on the TAS. Bounding an offset
alone leaves a separate obligation to account for the length of each write. -/

/-- The limit on `VRAM_Buffer1_Offset`. From here the last byte of a block entry, `$8B02`, still lands in the buffer. The TAS's 1-1 reaches 42. -/
def cleanLimit : UInt8 := 0x34

/-- The limit on `VRAM_Buffer2_Offset` during play: the buffer's size. The TAS reaches 29. -/
def cleanLimit2 : UInt8 := 0x21

/-- The limit on `VRAM_Buffer2_Offset` otherwise, which an area load reaches. -/
def loadLimit2 : UInt8 := 0x90

/-- The game is running a level, rather than loading one or showing a screen. -/
def inPlay (s : NES) : Bool := inGame s && byte s 0x772 == 3

def cleanAt (s : NES) : Bool :=
  byte s 0x300 ≤ cleanLimit && byte s 0x340 ≤ (if inPlay s then cleanLimit2 else loadLimit2)

/-- The assumption supplies the checker's hypothesis during play, for a contract whose bounds on the offsets allow everything up to the limits. -/
theorem clean_of_cleanAt {g : Smb.Abs.Global} (hg : ∀ v : UInt8, v ≤ cleanLimit → (Smb.Abs.gAt g 0x300).mem v = true)
    (hg2 : ∀ v : UInt8, v ≤ cleanLimit2 → (Smb.Abs.gAt g 0x340).mem v = true) {s : NES} (hp : inPlay s = true) (h : cleanAt s = true) :
    Smb.Abs.Clean g s := by
  simp only [cleanAt, hp, if_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨hg _ h.1, hg2 _ h.2⟩

/-- A frame's start. -/
def startFrame (b : UInt8) (s : NES) : NES := { s with pad0 := b, pad1 := 0, polls := 0, frameDone := false }

/-- Every instruction of a frame's loop, as `NES.frame.go` runs them, ends within the contract. -/
def goClean : Nat → NES → Bool
  | 0, _ => true
  | n + 1, s => s.frameDone || (cleanAt (CPU.step.run s).2 && goClean n (CPU.step.run s).2)

/-- Every instruction of a run ends within the contract. -/
def runClean : List UInt8 → NES → Bool
  | [], s => cleanAt s
  | b :: l, s => cleanAt s && goClean NES.frameFuel (startFrame b s) && runClean l (NES.frame b 0 s)

def NoOverflow (inputs : List UInt8) : Prop := runClean inputs initial = true

/-- A prefix of a clean run is clean. -/
theorem runClean_take (l : List UInt8) (s : NES) (j : Nat) (h : runClean l s = true) : runClean (l.take j) s = true := by
  induction l generalizing s j with
  | nil => simpa using h
  | cons b l ih =>
    simp only [runClean, Bool.and_eq_true] at h
    cases j with
    | zero => simpa [runClean] using h.1.1
    | succ j =>
      simp only [List.take_succ_cons, runClean, Bool.and_eq_true]
      exact ⟨h.1, ih _ _ h.2⟩

/-- The goal under the assumption, which `Deps` argues. -/
def CleanBound (n : Nat) : Prop :=
  ∀ inputs : List UInt8, inputs.length < n → NoOverflow inputs →
    left (NES.runFrames inputs initial) = false ∧ (NES.runFrames inputs initial).unmodelled = false

/-- What the full goal would still need: overflowing doesn't get out of 1-1 sooner, or out of the model. -/
def DirtyBound (n : Nat) : Prop :=
  ∀ inputs : List UInt8, inputs.length < n → ¬ NoOverflow inputs →
    left (NES.runFrames inputs initial) = false ∧ (NES.runFrames inputs initial).unmodelled = false

/-- The two cases give the goal. -/
theorem exitBound_of_cases {n : Nat} (hc : CleanBound n) (hd : DirtyBound n) : ExitBound n := by
  intro inputs hlen
  by_cases h : NoOverflow inputs
  · exact hc inputs hlen h
  · exact hd inputs hlen h

/-! ## Milestones

Each is the frame an event happens, not a state that lasts, so that "at least `w` frames later" makes sense. -/

inductive Node
  /-- Control starts at the level's start. -/
  | start
  /-- Control starts at the halfway point, after a death. -/
  | respawn
  /-- Going down the pipe to the bonus room. -/
  | pipe
  /-- Control starts in the bonus room. -/
  | bonus
  /-- Going into the bonus room's side pipe. -/
  | side
  /-- Control starts on the surface after the bonus room. -/
  | exitPipe
  /-- Dying before the halfway page, or after it. -/
  | dieEarly | dieLate
  /-- Grabbing the flag. -/
  | grab
  deriving DecidableEq, Repr

/-- Control begins: the entrance routine hands over to normal play. -/
def controlStarts (p s : NES) : Bool := inGame s && engine p == 7 && engine s == 8

/-- `GameEngineSubroutine` has just become `e`. -/
def enters (e : UInt8) (p s : NES) : Bool := inGame s && engine p != e && engine s == e

def dying (s : NES) : Bool := engine s == 6 || engine s == 0x0B
def grabbing (s : NES) : Bool := engine s == 4 || engine s == 5

/-- Whether this frame, with `p` the state before it and `s` after, is this milestone. -/
def Node.at : Node → NES → NES → Bool
  | .start, p, s => controlStarts p s && areaType s == 1 && pos s ≤ 10240
  | .respawn, p, s => controlStarts p s && areaType s == 1 && 10240 < pos s && pos s < 655360
  | .exitPipe, p, s => controlStarts p s && areaType s == 1 && 655360 ≤ pos s
  | .bonus, p, s => controlStarts p s && areaType s == 2
  | .pipe, p, s => enters 3 p s
  | .side, p, s => enters 2 p s
  | .dieEarly, p, s => inGame s && !dying p && dying s && byte s 0x71A < 5
  | .dieLate, p, s => inGame s && !dying p && dying s && 5 ≤ byte s 0x71A
  | .grab, p, s => inGame s && !grabbing p && grabbing s

/-- Milestone `a` happens on the frame that takes the run to `at' inputs i`. -/
def Hits (a : Node) (inputs : List UInt8) (i : Nat) : Prop :=
  a.at (at' inputs (i - 1)) (at' inputs i) = true

/-! ## The route graph -/

structure Edge where
  src : Node
  dst : Node
  w : Nat
  deriving DecidableEq, Repr

/-- The frames that matter. -/
def horizon : Nat := 1943

/-- What follows a grab depends on `Y` on the grab frame. A high grab slides 61–62 frames, then walks 92–103. A low one walks 126 with no slide. One in the walk-skip band (the full flagpole glitch) walks 1–2, which ends the level about 6 rules sooner than a low grab on the same frame. `Y` ≥ 168 can't grab: the side sensor reads the base block. -/
inductive GrabKind
  | high | low | skip
  deriving DecidableEq, Repr

def grabKind (s : NES) : GrabKind :=
  if byte s 0xCE < 162 then .high else if byte s 0xCE < 165 then .low else .skip

def anyGrab (_ : NES) : Bool := true

/-- From milestone `a`, a run that later makes a grab of the kind `P` first reaches one of `a`'s successors in `E`, at least the edge's weight later. -/
def Covers (P : NES → Bool) (E : List Edge) (a : Node) : Prop :=
  ∀ (inputs : List UInt8) (i j : Nat), i ≤ j → j < horizon → (at' inputs j).unmodelled = false → NoOverflow (inputs.take j) →
    Hits a inputs i → Hits .grab inputs j → P (at' inputs j) = true →
    ∃ e ∈ E, e.src = a ∧ ∃ i', i < i' ∧ i' ≤ j ∧ i + e.w ≤ i' ∧ Hits e.dst inputs i'

def nodes : List Node := [.start, .respawn, .pipe, .bonus, .side, .exitPipe, .dieEarly, .dieLate, .grab]

/-- `d` lower-bounds the time to the grab along `E`: a potential, so it needs no search to check. -/
def Feasible (E : List Edge) (d : Node → Nat) : Bool :=
  d .grab == 0 && E.all fun e => d e.src ≤ e.w + d e.dst

theorem grab_time {P : NES → Bool} {E : List Edge} {d : Node → Nat} (hf : Feasible E d = true) (hc : ∀ a, a ≠ .grab → Covers P E a)
    (k : Nat) (a : Node) (inputs : List UInt8) (i j : Nat) (hk : j - i ≤ k) (hij : i ≤ j) (hj : j < horizon)
    (hu : (at' inputs j).unmodelled = false) (hcl : NoOverflow (inputs.take j)) (ha : Hits a inputs i) (hg : Hits .grab inputs j)
    (hp : P (at' inputs j) = true) :
    i + d a ≤ j := by
  simp only [Feasible, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hf
  induction k generalizing a i with
  | zero =>
    by_cases hag : a = .grab
    · subst hag; omega
    · obtain ⟨e, _, _, i', h1, h2, _, _⟩ := hc a hag inputs i j hij hj hu hcl ha hg hp
      omega
  | succ k ih =>
    by_cases hag : a = .grab
    · subst hag; omega
    · obtain ⟨e, he, hs, i', h1, h2, h3, h4⟩ := hc a hag inputs i j hij hj hu hcl ha hg hp
      have h5 := ih e.dst i' (by omega) h2 h4
      have h6 := hf.2 e he
      rw [hs] at h6
      omega

/-- Pipe exit to the grab. A low grab's is the TAS's 240. A high or skip grab can come sooner (`high_grab_witness` takes 234), so they get 213, under the 226 the speed and acceleration limits give for reaching the pole's column at any height (`flag_edge`). -/
def lastEdge : GrabKind → Nat
  | .low => 240
  | _ => 213

/-- The graph up to a grab of kind `k`, with the TAS's times on its path. The weights off that path only have to be true: `dist` needs no more. Only the last stretch depends on the kind. -/
def edges (k : GrabKind) : List Edge :=
  [⟨.start, .pipe, 368⟩, ⟨.pipe, .bonus, 91⟩, ⟨.bonus, .side, 111⟩, ⟨.side, .exitPipe, 282⟩, ⟨.exitPipe, .grab, lastEdge k⟩,
   -- walking past the pipe
   ⟨.start, .grab, 1249⟩,
   -- dying sends Mario back
   ⟨.start, .dieEarly, 1⟩, ⟨.bonus, .dieEarly, 1⟩, ⟨.dieEarly, .start, 1⟩,
   ⟨.start, .dieLate, 496⟩, ⟨.exitPipe, .dieLate, 1⟩, ⟨.dieLate, .respawn, 155⟩, ⟨.respawn, .dieLate, 1⟩,
   ⟨.respawn, .grab, 736⟩]

/-- Frames left to a grab of kind `k` from each milestone. -/
def dist (k : GrabKind) : Node → Nat
  | .start => 852 + lastEdge k | .pipe => 484 + lastEdge k | .bonus => 393 + lastEdge k | .side => 282 + lastEdge k
  | .exitPipe => lastEdge k | .grab => 0
  | .dieEarly => 851 + lastEdge k | .dieLate => 891 | .respawn => 736

theorem dist_feasible (k : GrabKind) : Feasible (edges k) (dist k) = true := by cases k <;> decide

/-- The earliest frame a grab of kind `k` can come, given control no sooner than frame 195. -/
def earliestGrab (k : GrabKind) : Nat := 195 + dist k .start

theorem earliestGrab_eq : earliestGrab .low = 1287 ∧ earliestGrab .high = 1260 ∧ earliestGrab .skip = 1260 := by decide

/-- Everything left to prove for runs that don't overflow. -/
structure Deps : Prop where
  supported : ∀ inputs : List UInt8, inputs.length < horizon → NoOverflow inputs → (NES.runFrames inputs initial).unmodelled = false
  firstControl : ∀ (inputs : List UInt8) (j : Nat), j < horizon → NoOverflow (inputs.take j) → left (at' inputs j) = true →
    ∃ i, 195 ≤ i ∧ i ≤ j ∧ Hits .start inputs i
  grabFirst : ∀ (inputs : List UInt8) (i j : Nat), i ≤ j → j < horizon → NoOverflow (inputs.take j) → Hits .start inputs i → left (at' inputs j) = true →
    ∃ G, i ≤ G ∧ G ≤ j ∧ Hits .grab inputs G
  /-- Up to a grab of kind `k`, each milestone goes on to one of `edges k`' successors, no sooner than the edge's weight. -/
  covers : ∀ k a, a ≠ .grab → Covers (fun s => grabKind s == k) (edges k) a
  /-- A grab of kind `k` no sooner than `earliestGrab k` doesn't leave 1-1 before the TAS. For a skip grab this is the
  walk skip's real obligation: it may exist, as long as it comes too late to gain. It saves about 126 frames, six rules,
  against a low grab on the same frame, so roughly frame 1,413 or later; the exact frame depends on the timer and isn't
  computed. `flagSkip_of_noSkip` shows the old claim that it never happens is stronger. -/
  flag : ∀ k (inputs : List UInt8) (G n : Nat), G ≤ n → n < horizon → NoOverflow (inputs.take n) → Hits .grab inputs G →
    earliestGrab k ≤ G → grabKind (at' inputs G) = k → left (at' inputs n) = false

theorem take_length_le (inputs : List UInt8) (j : Nat) : (inputs.take j).length ≤ j := by
  rw [List.length_take]; omega

/-- **The argument.** If everything in `Deps` holds, then no run that keeps the VRAM buffers from overflowing beats the TAS's 1-1. -/
theorem oneOne_of_deps (h : Deps) : CleanBound horizon := by
  intro inputs hlen hclean
  have hs : NES.runFrames inputs initial = at' inputs inputs.length := by simp [at']
  have hcl : ∀ j, NoOverflow (inputs.take j) := fun j => runClean_take _ _ j hclean
  have hsup : ∀ j, j < horizon → (at' inputs j).unmodelled = false := fun j hj =>
    h.supported _ (Nat.lt_of_le_of_lt (take_length_le inputs j) hj) (hcl j)
  rw [hs]
  refine ⟨?_, hsup _ hlen⟩
  cases hl : left (at' inputs inputs.length) with
  | false => rfl
  | true =>
    obtain ⟨i, hi, hij, hst⟩ := h.firstControl inputs _ hlen (hcl _) hl
    obtain ⟨G, hG1, hG2, hgr⟩ := h.grabFirst inputs i _ hij hlen (hcl _) hst hl
    have hGh : G < horizon := Nat.lt_of_le_of_lt hG2 hlen
    have ht := grab_time (dist_feasible _) (h.covers (grabKind (at' inputs G))) (G - i) .start inputs i G (Nat.le_refl _) hG1 hGh
      (hsup G hGh) (hcl G) hst hgr (beq_self_eq_true _)
    have ht' : earliestGrab (grabKind (at' inputs G)) ≤ G := by
      simp only [earliestGrab]
      omega
    have h0 := h.flag _ inputs G _ hG2 hlen (hcl _) hgr ht' rfl
    rw [hl] at h0
    cases h0

/-- The old field `noSkip`, that no grab is ever in the walk-skip band, gives the skip case of `flag` outright. -/
theorem flagSkip_of_noSkip
    (h : ∀ (inputs : List UInt8) (G : Nat), G < horizon → NoOverflow (inputs.take G) → Hits .grab inputs G → byte (at' inputs G) 0xCE < 165)
    (inputs : List UInt8) (G n : Nat) (hGn : G ≤ n) (hn : n < horizon) (hcl : NoOverflow (inputs.take n)) (hgr : Hits .grab inputs G)
    (hk : grabKind (at' inputs G) = .skip) : left (at' inputs n) = false := by
  have hclG : NoOverflow (inputs.take G) := by
    have := runClean_take (inputs.take n) initial G hcl
    rwa [List.take_take, Nat.min_eq_left hGn] at this
  have hy := h inputs G (Nat.lt_of_le_of_lt hGn hn) hclG hgr
  simp only [grabKind] at hk
  repeat' split at hk
  all_goals first | cases hk | contradiction

/-! ## The speed limit alone -/

/-- `n` player updates take the run from frame `i` to frame `j`, each within the speed limit, with nothing between them adding progress. Everything `minimum_updates` needs. -/
def SpeedLimited (inputs : List UInt8) (i j n : Nat) : Prop :=
  n ≤ j - i ∧ i ≤ j ∧ ∃ entry out : Nat → UInt16 → UInt8,
    entry 0 = ramAt (at' inputs i) ∧ entry n = ramAt (at' inputs j) ∧
    (∀ k, k ≤ n → InWindow (entry k)) ∧ (∀ k, k < n → InWindow (out k)) ∧
    (∀ k, k < n → XStep (entry k) (out k)) ∧
    (∀ k, k < n → (phi (entry (k + 1))).toNat ≤ (phi (out k)).toNat)

/-- Where `HorizontalDistance` enters: an ordinary stretch covering `D` takes at least `⌈D/640⌉` frames. -/
theorem speed_edge {inputs : List UInt8} {i j n D : Nat} (h : SpeedLimited inputs i j n)
    (hd : pos (at' inputs i) + D ≤ pos (at' inputs j)) : i + (D + 639) / 640 ≤ j := by
  obtain ⟨hn, hij, entry, out, h0, hN, hw, ho, hs, hr⟩ := h
  have := minimum_frames entry out n D (j - i) hw ho hs hr (by simpa [pos, h0, hN] using hd) hn
  omega

/-- The graph with only the speed limit's weights. The bonus room's 70 and the pipe's 351 assume the positions in `docs/lower-bound-1-1.md`; the scripted edges are as `edges`. -/
def speedEdges : List Edge :=
  [⟨.start, .pipe, 351⟩, ⟨.pipe, .bonus, 91⟩, ⟨.bonus, .side, 70⟩, ⟨.side, .exitPipe, 282⟩, ⟨.exitPipe, .grab, 217⟩,
   ⟨.start, .grab, 1249⟩,
   ⟨.start, .dieEarly, 1⟩, ⟨.bonus, .dieEarly, 1⟩, ⟨.dieEarly, .start, 1⟩,
   ⟨.start, .dieLate, 496⟩, ⟨.exitPipe, .dieLate, 1⟩, ⟨.dieLate, .respawn, 155⟩, ⟨.respawn, .dieLate, 1⟩,
   ⟨.respawn, .grab, 736⟩]

def speedDist : Node → Nat
  | .start => 1011 | .pipe => 660 | .bonus => 569 | .side => 499 | .exitPipe => 217 | .grab => 0
  | .dieEarly => 1010 | .dieLate => 891 | .respawn => 736

theorem speedDist_feasible : Feasible speedEdges speedDist = true := by decide

/-- With the speed limit's weights the grab is at frame 1,206 or later, against the TAS's 1,287: all the rest of the gap is launches, the bonus room's fall and the flag approach. -/
theorem speed_grab (hc : ∀ a, a ≠ .grab → Covers anyGrab speedEdges a) (inputs : List UInt8) (i G : Nat) (hi : 195 ≤ i) (hG : i ≤ G)
    (hh : G < horizon) (hu : (at' inputs G).unmodelled = false) (hcl : NoOverflow (inputs.take G)) (hst : Hits .start inputs i) (hgr : Hits .grab inputs G) :
    1206 ≤ G := by
  have ht := grab_time speedDist_feasible hc (G - i) .start inputs i G (Nat.le_refl _) hG hh hu hcl hst hgr rfl
  have : speedDist .start = 1011 := rfl
  omega

/-! ## The speed limit and the acceleration limit -/

/-- As `SpeedLimited`, from rest, and with the acceleration limit on the updates where it binds. -/
def LaunchLimited (inputs : List UInt8) (i j n : Nat) : Prop :=
  n ≤ j - i ∧ i ≤ j ∧ ∃ entry out : Nat → UInt16 → UInt8,
    entry 0 = ramAt (at' inputs i) ∧ entry n = ramAt (at' inputs j) ∧
    (∀ k, k ≤ n → InWindow (entry k)) ∧ (∀ k, k < n → InWindow (out k)) ∧
    (∀ k, k < n → XStep (entry k) (out k)) ∧
    (∀ k, k < n → k < 23 → LStep (entry k) (out k)) ∧
    (∀ k, k < n → (phi (entry (k + 1))).toNat ≤ (phi (out k)).toNat) ∧
    (∀ k, k < n → upSpeed (entry (k + 1)) ≤ upSpeed (out k)) ∧
    (upSpeed (ramAt (at' inputs i))).toNat ≤ 255

/-- Where `Launch` enters: a stretch from rest covering more than `gain m` takes more than `m` frames. -/
theorem launch_edge {inputs : List UInt8} {i j n m D : Nat} (h : LaunchLimited inputs i j n)
    (hd : pos (at' inputs i) + D ≤ pos (at' inputs j)) (hm : gain m < D) : i + (m + 1) ≤ j := by
  obtain ⟨hn, hij, entry, out, h0, hN, hw, ho, hs, hl, hr, hu, hr0⟩ := h
  have := launch_updates entry out n m D hw ho hs hl hr hu (by rw [h0]; exact hr0) (by simpa [pos, h0, hN] using hd) hm
  omega

/-- The stretches `speedEdges` measures, from rest. -/
theorem pipe_edge {inputs : List UInt8} {i j n : Nat} (h : LaunchLimited inputs i j n)
    (hd : pos (at' inputs i) + 224256 ≤ pos (at' inputs j)) : i + 360 ≤ j := launch_edge h hd gain_pipe
theorem bonus_edge {inputs : List UInt8} {i j n : Nat} (h : LaunchLimited inputs i j n)
    (hd : pos (at' inputs i) + 44224 ≤ pos (at' inputs j)) : i + 79 ≤ j := launch_edge h hd gain_bonus
theorem flag_edge {inputs : List UInt8} {i j n : Nat} (h : LaunchLimited inputs i j n)
    (hd : pos (at' inputs i) + 138752 ≤ pos (at' inputs j)) : i + 226 ≤ j := launch_edge h hd gain_flag

/-! ## The frame contract

What the movement theorems ask of a run, as one statement about each frame. Stated from one frame's end to the next, nothing lies between the updates, so `SpeedLimited`'s and `LaunchLimited`'s clauses about the gaps hold outright. -/

/-- One frame stays in the window and within the speed limit. -/
def FrameLimited (inputs : List UInt8) (f : Nat) : Prop :=
  InWindow (ramAt (at' inputs f)) ∧ InWindow (ramAt (at' inputs (f + 1))) ∧
    XStep (ramAt (at' inputs f)) (ramAt (at' inputs (f + 1)))

/-- `FrameLimited` with the acceleration limit too. -/
def FrameLaunch (inputs : List UInt8) (f : Nat) : Prop :=
  FrameLimited inputs f ∧ LStep (ramAt (at' inputs f)) (ramAt (at' inputs (f + 1)))

/-- A stretch of limited frames is what `speed_edge` needs. -/
theorem speedLimited_of_frames {inputs : List UInt8} {i j : Nat} (hij : i ≤ j) (h0 : InWindow (ramAt (at' inputs i)))
    (h : ∀ f, i ≤ f → f < j → FrameLimited inputs f) : SpeedLimited inputs i j (j - i) := by
  refine ⟨Nat.le_refl _, hij, fun k => ramAt (at' inputs (i + k)), fun k => ramAt (at' inputs (i + k + 1)), rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show ramAt (at' inputs (i + (j - i))) = ramAt (at' inputs j)
    rw [Nat.add_sub_cancel' hij]
  · intro k hk
    cases k with
    | zero => exact h0
    | succ k => exact (h (i + k) (by omega) (by omega)).2.1
  · intro k hk
    exact (h (i + k) (by omega) (by omega)).2.1
  · intro k hk
    exact (h (i + k) (by omega) (by omega)).2.2
  · intro k _
    exact Nat.le_refl _

/-- A launch of limited frames, from rest, is what `launch_edge` needs. -/
theorem launchLimited_of_frames {inputs : List UInt8} {i j : Nat} (hij : i ≤ j) (h0 : InWindow (ramAt (at' inputs i)))
    (hr : (upSpeed (ramAt (at' inputs i))).toNat ≤ 255) (h : ∀ f, i ≤ f → f < j → FrameLaunch inputs f) :
    LaunchLimited inputs i j (j - i) := by
  refine ⟨Nat.le_refl _, hij, fun k => ramAt (at' inputs (i + k)), fun k => ramAt (at' inputs (i + k + 1)), rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hr⟩
  · show ramAt (at' inputs (i + (j - i))) = ramAt (at' inputs j)
    rw [Nat.add_sub_cancel' hij]
  · intro k hk
    cases k with
    | zero => exact h0
    | succ k => exact (h (i + k) (by omega) (by omega)).1.2.1
  · intro k hk
    exact (h (i + k) (by omega) (by omega)).1.2.1
  · intro k hk
    exact (h (i + k) (by omega) (by omega)).1.2.2
  · intro k hk _
    exact (h (i + k) (by omega) (by omega)).2
  · intro k _
    exact Nat.le_refl _
  · intro k _
    exact UInt16.le_refl _

/-- The graph with the speed and acceleration limits' weights. -/
def launchEdges : List Edge :=
  [⟨.start, .pipe, 360⟩, ⟨.pipe, .bonus, 91⟩, ⟨.bonus, .side, 79⟩, ⟨.side, .exitPipe, 282⟩, ⟨.exitPipe, .grab, 226⟩,
   ⟨.start, .grab, 1249⟩,
   ⟨.start, .dieEarly, 1⟩, ⟨.bonus, .dieEarly, 1⟩, ⟨.dieEarly, .start, 1⟩,
   ⟨.start, .dieLate, 496⟩, ⟨.exitPipe, .dieLate, 1⟩, ⟨.dieLate, .respawn, 155⟩, ⟨.respawn, .dieLate, 1⟩,
   ⟨.respawn, .grab, 736⟩]

def launchDist : Node → Nat
  | .start => 1038 | .pipe => 678 | .bonus => 587 | .side => 508 | .exitPipe => 226 | .grab => 0
  | .dieEarly => 1037 | .dieLate => 891 | .respawn => 736

theorem launchDist_feasible : Feasible launchEdges launchDist = true := by decide

/-- With those weights the grab is at frame 1,233 or later, against the TAS's 1,287. -/
theorem launch_grab (hc : ∀ a, a ≠ .grab → Covers anyGrab launchEdges a) (inputs : List UInt8) (i G : Nat) (hi : 195 ≤ i) (hG : i ≤ G)
    (hh : G < horizon) (hu : (at' inputs G).unmodelled = false) (hcl : NoOverflow (inputs.take G)) (hst : Hits .start inputs i) (hgr : Hits .grab inputs G) :
    1233 ≤ G := by
  have ht := grab_time launchDist_feasible hc (G - i) .start inputs i G (Nat.le_refl _) hG hh hu hcl hst hgr rfl
  have : launchDist .start = 1038 := rfl
  omega

/-! ## The TAS

These aren't assumptions: they run the model, and show the statement is tight and its milestones are the ones the TAS passes. -/

/-- Each frame of a run up to `n` that hits a milestone: its index, as in `at'`, and the milestone. -/
def milestones (inputs : List UInt8) (n : Nat) : List (Nat × Node) := Id.run do
  let mut p := initial
  let mut out : List (Nat × Node) := []
  for i in [0:n] do
    let s := NES.frame (inputs.getD i 0) 0 p
    for a in nodes do
      if a.at p s then out := (i + 1, a) :: out
    p := s
  return out.reverse

/-- The TAS passes the milestones of `edges`, once each, at frames whose differences are the edges' weights. -/
theorem tas_milestones :
    milestones tasInputs 1943 = [(195, .start), (563, .pipe), (654, .bonus), (765, .side), (1047, .exitPipe), (1287, .grab)] := by
  native_decide

/-- The TAS's 1-1 meets the assumption at every instruction, so the assumption keeps the bound's witness. -/
theorem tas_clean : NoOverflow (tasInputs.take 1943) := by
  unfold NoOverflow
  native_decide

/-- The TAS's grab, just below the walk-skip band. -/
theorem tas_grab_y : byte (at' tasInputs 1287) 0xCE = 164 := by native_decide

/-- So it's a low grab, on its kind's earliest frame. -/
theorem tas_grab_kind : grabKind (at' tasInputs 1287) = .low := by native_decide

/-- The TAS to surface control, then a path found by search, then nothing. -/
def highGrabInputs : List UInt8 :=
  tasInputs.take 1047 ++ [0xC0, 0xC1, 0x82, 0x80, 0xC2, 0xC0, 0x81, 0xC1, 0x81, 0xC3, 0xC2, 0xC1, 0x81, 0xC1, 0xC1, 0x80, 0x80, 0xC0, 0x82, 0x81, 0x81, 0x03, 0x82, 0x42, 0xC0, 0xC3, 0x81, 0xC1, 0xC3, 0xC1, 0x80, 0x80, 0x03, 0x03, 0x01, 0x82, 0xC0, 0xC1, 0x02, 0xC2, 0xC0, 0x03, 0x82, 0x83, 0xC0, 0x01, 0x03, 0x01, 0x01, 0x83, 0xC1, 0x82, 0x83, 0x80, 0x03, 0x00, 0xC3, 0x00, 0x01, 0x81, 0x00, 0x83, 0x00, 0x03, 0xC3, 0xC2, 0x00, 0x03, 0xC3, 0xC0, 0x03, 0x02, 0x01, 0x02, 0x03, 0x00, 0x01, 0x01, 0x82, 0x03, 0x02, 0x03, 0x83, 0x01, 0xC2, 0x01, 0x01, 0x03, 0x00, 0x02, 0x02, 0x02, 0x02, 0x03, 0x03, 0x00, 0x83, 0x02, 0x03, 0xC1, 0x01, 0x01, 0x01, 0x03, 0xC0, 0xC3, 0x81, 0x81, 0xC3, 0x82, 0x82, 0x81, 0x80, 0xC0, 0x02, 0x00, 0xC3, 0xC3, 0x83, 0xC0, 0x81, 0x81, 0xC0, 0x03, 0xC1, 0xC3, 0x83, 0x83, 0x83, 0xC0, 0x01, 0x83, 0xC2, 0x02, 0x01, 0x81, 0xC2, 0x03, 0x01, 0xC2, 0x80, 0xC3, 0xC1, 0x80, 0x03, 0x03, 0x83, 0x81, 0xC1, 0x01, 0x01, 0x03, 0x03, 0xC3, 0x80, 0xC3, 0xC2, 0x03, 0xC0, 0x00, 0x03, 0x02, 0x82, 0xC2, 0x83, 0xC0, 0x81, 0xC1, 0xC3, 0xC1, 0x83, 0x03, 0x02, 0xC1, 0x81, 0xC0, 0x81, 0x03, 0x01, 0x82, 0x01, 0x80, 0x81, 0x80, 0x03, 0xC0, 0x80, 0x00, 0x03, 0x03, 0x01, 0x02, 0x03, 0x82, 0xC1, 0xC2, 0xC3, 0x01, 0xC0, 0xC3, 0x81, 0x81, 0xC1, 0x02, 0xC2, 0x83, 0x01, 0x02, 0xC2, 0xC2, 0x02, 0xC1, 0x01, 0x03, 0x83, 0x81, 0x00, 0x80, 0x81, 0x81, 0x03, 0xC1, 0x02, 0x03, 0x03, 0x01, 0xC3, 0x80, 0xC0, 0x01, 0xC0, 0x03, 0x01, 0x43] ++ List.replicate 700 0

/-- A run within the assumption that goes from pipe exit to a grab in 234 frames, 6 under the TAS's, at `Y` 138, and leaves 1-1 a rule later than the TAS. So an edge of 240 is false for high grabs, and grabbing sooner isn't enough. -/
theorem high_grab_witness :
    Hits .exitPipe highGrabInputs 1047 ∧ Hits .grab highGrabInputs 1281 ∧ byte (at' highGrabInputs 1281) 0xCE = 138 ∧
      NoOverflow (highGrabInputs.take 1964) ∧ left (at' highGrabInputs 1963) = false ∧ left (at' highGrabInputs 1964) = true := by
  unfold Hits NoOverflow
  native_decide

theorem tas_leaves : left (at' tasInputs 1943) = true ∧ (at' tasInputs 1943).unmodelled = false := by native_decide

theorem tas_stays : left (at' tasInputs 1942) = false := by native_decide

/-- The goal can't ask for more. -/
theorem exitBound_tight : ¬ ExitBound 1944 := by
  intro h
  have hlen : (tasInputs.take 1943).length < 1944 := by native_decide
  have := (h _ hlen).1
  have h2 := tas_leaves.1
  simp only [at'] at h2
  rw [h2] at this
  cases this

end Smb.Goal
