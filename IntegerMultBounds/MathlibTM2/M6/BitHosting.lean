module

public import IntegerMultBounds.MathlibTM2.M6.BitSchedule
public import IntegerMultBounds.Networks.Certificates.PR589.Nine.PortLabels
public import IntegerMultBounds.Networks.Certificates.PR589.Nine.Flag

/-!
# The hosted slots of the nine-stage node

Every helper residual of every stage is hosted on the pending coordinates of an idle data family
(upstream `emit_k.py` with the frozen selection `selection9-p111.json`). This file expands the
selection into explicit slots and checks their geometry.

**Levels.** `levelRun` replays the schedule with each pair's level, the number of stages its data
has advanced through. Every sweep of stage `s` finds its pair at level `s`, every bridge joins
pairs at equal levels, every idle advances its pair to the current stage at rank `7` per stage,
and all pairs reach level `9` before the exchange. `idleLevels` lists each idle's source and target
level, so its pending projector is `span (7a) (7b)` (`Flag.pending_source`, `pending_target`).

**Slots.** `slots` is upstream's expansion order: idles in order, copy positions in order (the
copies hosting more residuals first), eight-wide slots from offset `0`, stages consumed in the
frozen order, and helpers numbered stage by stage. `slots_fingerprint` matches upstream's emitted
slot list. Each slot
* lies in its idle's window (`slot_in_window`), off the active pair (`slot_off_active`);
* fits inside the pending interval at an offset `8j`, `j < 5` (`slot_fits`);
* hosts one helper, and every helper of every stage is hosted exactly once (`slot_helpers`).
Distinct slots differ in idle, copy or offset (`slot_key_injective`).

**Classes.** Within one invocation a family can host up to five helpers, on different slots of one
idle (`same_pair_windows`). Upstream separates them by cover classes of the orthogonal group. Here
each family's rows are split into five classes, and in the class-`d` run of an invocation the helper
on a slot with offset `8j` uses class `d + j mod 5` of its host family (`hostClass`):
`hostClass_distinct` gives distinct physical owners within a run, and `hostClass_bijective` gives
each class every residual once over the five runs.

**Exchanges.** `idle_pending`: an idle's advance is the interval `span (7a) (7b)` on both sides.
`idle_hosting`: on every copy, its exchange is the product of the exchanges on the hosted slots
(`slot_in_pending`, `slot_chart`) and on the remainder, which has rank `7(b - a) - 8k`
(`rank_remainder`). `remainders_perm`: these remainders are the occurrence list's. Helpers start in frame `0` and end in the full frame
(`helper_frames`), so a hosted helper's local frames lift through `slotChart` to `0` and the slot
projector, and its MOVEs keep their ranks (`Flag.rank_slot_sub`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.BitHosting

open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open IntegerMultBounds.MathlibTM2.M6.BitOccurrences
open IntegerMultBounds.MathlibTM2.M6.BitSchedule
open scoped Matrix

/-! ### Levels -/

/-- The pair levels, the level of the last sweep, and the source and target level of each idle so
far. -/
structure LevelState where
  levels : List ℕ
  current : ℕ
  idles : List (ℕ × ℕ)
  deriving DecidableEq

/-- One schedule entry; `none` if the entry finds a pair at the wrong level. -/
def levelStep : Option LevelState → Entry → Option LevelState
  | none, _ => none
  | some st, .sweep s p =>
      if st.levels.getD p 0 = s then
        some { st with levels := st.levels.set p (s + 1), current := s + 1 }
      else none
  | some st, .idle p r =>
      let a := st.levels.getD p 0
      if a ≤ st.current ∧ r = 7 * (st.current - a) then
        some { st with levels := st.levels.set p st.current, idles := st.idles ++ [(a, st.current)] }
      else none
  | some st, .bridge d s =>
      if st.levels.getD d 0 = st.levels.getD s 0 then some st else none
  | some st, .exchange => if st.levels.all (· = 9) then some st else none

def levelRun : Option LevelState := (schedule 4).foldl levelStep (some ⟨[0, 0, 0, 0], 0, []⟩)

/-- The source and target level of each idle. -/
def idleLevels : List (ℕ × ℕ) :=
  [(0, 2), (2, 3), (0, 4), (4, 5), (0, 6), (6, 7), (3, 9), (5, 9), (7, 9), (9, 9)]

/-- The schedule's level replay: every entry is admissible, all pairs end at level `9`, and the
idles have the listed levels. -/
theorem levelRun_eq : levelRun = some ⟨[9, 9, 9, 9], 9, idleLevels⟩ := by
  decide +kernel

theorem idleLevels_ranks : idleLevels.map (fun l => 7 * (l.2 - l.1)) = idleRanks 4 := by
  decide +kernel

/-! ### Slots -/

/-- A hosted slot: idle, copy position `side·111 + port`, offset in the pending interval, stage,
helper. -/
structure Slot where
  idle : ℕ
  copy : ℕ
  offset : ℕ
  stage : ℕ
  helper : ℕ
  deriving DecidableEq, Repr

/-- The number of residuals hosted on each copy of idle `i`, hosting copies first. -/
def copyCounts (i : ℕ) : List ℕ :=
  let ps := patterns.filter (·.1 = i)
  (ps.filter (·.2.1 ≠ []) ++ ps.filter (·.2.1 = [])).flatMap
    fun p => List.replicate p.2.2 p.2.1.length

/-- The stages of the residuals hosted into idle `i`, in the frozen order. -/
def idleStages (i : ℕ) : List ℕ :=
  (stageCounts.filter (·.1 = i)).flatMap fun e => List.replicate e.2.2.2 e.2.2.1

/-- The copy and offset of each slot of idle `i`. -/
def idlePositions (i : ℕ) : List (ℕ × ℕ) :=
  (copyCounts i).zipIdx.flatMap fun x => (List.range x.1).map fun j => (x.2, 8 * j)

/-- Numbers the helpers of each stage in order; `next` holds the next helper of each stage. -/
def numberHelpers : List (ℕ × ℕ × ℕ × ℕ) → List ℕ → List Slot
  | [], _ => []
  | (i, c, o, s) :: rest, next =>
      ⟨i, c, o, s, next.getD s 0⟩ :: numberHelpers rest (next.set s (next.getD s 0 + 1))

def unnumbered : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range 9).flatMap fun i =>
    ((idlePositions i).zip (idleStages i)).map fun x => (i, x.1.1, x.1.2, x.2)

def slots : List Slot := numberHelpers unnumbered (List.replicate 9 0)

theorem positions_stages : ∀ i < 9, (idlePositions i).length = (idleStages i).length := by
  decide +kernel

theorem slots_length : slots.length = 3951 := by
  decide +kernel

def fingerprint (l : List Slot) : ℕ :=
  (l.zipIdx.map fun x =>
    (x.2 + 1) * (((((x.1.idle * 222 + x.1.copy) * 64 + x.1.offset) * 9 + x.1.stage) * 439) +
      x.1.helper)).sum

/-- The slots are upstream's emitted slot list. -/
theorem slots_fingerprint : fingerprint slots = 2811893901606714 := by
  decide +kernel

/-- The pair of idle `i`. -/
def pairOf (i : ℕ) : ℕ := ((windows (schedule 4)).getD i (0, 0, [])).1

/-- The window of idle `i`. -/
def windowOf (i : ℕ) : List ℕ := ((windows (schedule 4)).getD i (0, 0, [])).2.2

/-- The pair swept at stage `s`. -/
def activePair (s : ℕ) : ℕ := (s - 1) / 2

theorem activePair_schedule : (schedule 4).filterMap (fun e => match e with
    | .sweep s p => some (s, p) | _ => none) = (List.range 9).map fun s => (s, activePair s) := by
  decide +kernel

theorem slot_in_window : ∀ σ ∈ slots, σ.stage ∈ windowOf σ.idle := by
  decide +kernel

theorem slot_off_active : ∀ σ ∈ slots, pairOf σ.idle ≠ activePair σ.stage := by
  decide +kernel

theorem slot_fits : ∀ σ ∈ slots, σ.idle < 9 ∧ σ.copy < 222 ∧ σ.stage < 9 ∧ σ.offset % 8 = 0 ∧
    σ.offset < 40 ∧ σ.offset + 8 ≤ (idleRanks 4).getD σ.idle 0 := by
  decide +kernel

/-- Every helper of every stage is hosted exactly once, in order. -/
theorem slot_helpers : ∀ s < 9, (slots.filter (·.stage = s)).map (·.helper) = List.range 439 := by
  decide +kernel

/-- The slots in order of idle, copy and offset. -/
theorem slot_positions : slots.map (fun σ => (σ.idle, σ.copy, σ.offset)) =
    (List.range 9).flatMap fun i => (idlePositions i).map fun x => (i, x.1, x.2) := by
  decide +kernel

def slotKey (σ : Slot) : ℕ := (σ.idle * 222 + σ.copy) * 64 + σ.offset

theorem isChain_of_zip : ∀ {l : List ℕ}, (∀ x ∈ l.zip l.tail, x.1 < x.2) →
    List.IsChain (· < ·) l
  | [], _ => .nil
  | [_], _ => .singleton _
  | a :: b :: t, h => by
    rw [List.isChain_cons_cons]
    refine ⟨h (a, b) (by simp), isChain_of_zip fun x hx => h x ?_⟩
    simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
    exact Or.inr hx

theorem slot_keys_step : ∀ x ∈ (slots.map slotKey).zip (slots.map slotKey).tail, x.1 < x.2 := by
  decide +kernel

theorem slot_keys_increasing : List.IsChain (· < ·) (slots.map slotKey) :=
  isChain_of_zip slot_keys_step

/-- Distinct slots differ in idle, copy or offset. -/
theorem slot_key_injective : ∀ σ ∈ slots, ∀ τ ∈ slots, slotKey σ = slotKey τ → σ = τ :=
  List.inj_on_of_nodup_map (List.sortedLT_iff_isChain.mpr slot_keys_increasing).nodup

/-- Two idles of one pair have disjoint windows, so a family hosts residuals of one stage on one
idle only. -/
theorem same_pair_windows_check : ∀ i < 10, ∀ j < 10,
    i = j ∨ pairOf i ≠ pairOf j ∨ ∀ s ∈ windowOf i, s ∉ windowOf j := by
  decide +kernel

theorem same_pair_windows (i : ℕ) (hi : i < 10) (j : ℕ) (hj : j < 10) (hij : i ≠ j)
    (hpair : pairOf i = pairOf j) : ∀ s ∈ windowOf i, s ∉ windowOf j := by
  rcases same_pair_windows_check i hi j hj with h | h | h
  · exact absurd h hij
  · exact absurd hpair h
  · exact h

/-! ### Host classes -/

/-- The host class of a slot in the class-`d` run of its invocation. -/
def hostClass (σ : Slot) (d : ℕ) : ℕ := (d + σ.offset / 8) % 5

/-- Within one run, the helpers of a stage hosted on one family use distinct classes. -/
theorem hostClass_distinct (σ τ : Slot) (hσ : σ ∈ slots) (hτ : τ ∈ slots)
    (hstage : σ.stage = τ.stage) (hpair : pairOf σ.idle = pairOf τ.idle) (hcopy : σ.copy = τ.copy)
    (hne : σ ≠ τ) (d : ℕ) : hostClass σ d ≠ hostClass τ d := by
  have hidle : σ.idle = τ.idle := by
    by_contra hij
    have hfσ := slot_fits σ hσ
    have hfτ := slot_fits τ hτ
    exact same_pair_windows σ.idle (by omega) τ.idle (by omega) hij hpair σ.stage
      (slot_in_window σ hσ) (hstage ▸ slot_in_window τ hτ)
  have hoff : σ.offset ≠ τ.offset := by
    intro ho
    apply hne
    apply slot_key_injective σ hσ τ hτ
    simp only [slotKey, hidle, hcopy, ho]
  have hfσ := slot_fits σ hσ
  have hfτ := slot_fits τ hτ
  simp only [hostClass]
  omega

/-- Over the five runs, a slot uses every class of its host family once. -/
theorem hostClass_bijective (σ : Slot) :
    Function.Bijective fun d : Fin 5 => (⟨hostClass σ d.val, Nat.mod_lt _ (by norm_num)⟩ : Fin 5) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  intro d e hde
  simp only [hostClass, Fin.mk.injEq] at hde
  apply Fin.ext
  omega

/-! ### Frames and exchanges -/

/-- Helpers start in frame `0` and end in the full frame. -/
theorem helper_frames : ∀ h < 439, Frames.initialRefs (222 + h) = 0 ∧ Frames.finalRefs (222 + h) = 1 := by
  decide +kernel

def idleSource (i : ℕ) : ℕ := (idleLevels.getD i (0, 0)).1

def idleTarget (i : ℕ) : ℕ := (idleLevels.getD i (0, 0)).2

/-- The number of residuals hosted on copy `c` of idle `i`. -/
def copyCount (i c : ℕ) : ℕ := (copyCounts i).getD c 0

theorem copyCount_fit : ∀ i < 9, idleTarget i ≤ 9 ∧ ∀ c < 222,
    idleSource i ≤ idleTarget i ∧ 8 * copyCount i c ≤ 7 * (idleTarget i - idleSource i) := by
  decide +kernel

/-- Each slot lies inside its idle's pending interval. -/
theorem slot_in_pending : ∀ σ ∈ slots,
    7 * idleSource σ.idle + σ.offset + 8 ≤ 7 * idleTarget σ.idle ∧ idleTarget σ.idle ≤ 9 := by
  decide +kernel

/-- The position of a slot in the pending order of its host family. -/
def slotPos (σ : Slot) : ℕ := 7 * idleSource σ.idle + σ.offset

/-- A hosted helper's chart is an isometric embedding onto its slot. -/
theorem slot_chart (σ : Slot) (hσ : σ ∈ slots) (t : ℕ) (ht : t < 111) :
    ((port t).slotChart (slotPos σ))ᵀ * (port t).slotChart (slotPos σ) = 1 ∧
      (port t).slotChart (slotPos σ) * ((port t).slotChart (slotPos σ))ᵀ =
        (port t).span (slotPos σ) (slotPos σ + 8) := by
  have hp := slot_in_pending σ hσ
  exact ⟨PortCertificate.slotChart_orthonormal (port_checked t ht) (by simp only [slotPos]; omega),
    PortCertificate.slotChart_proj _⟩

/-- On every copy, the exchange of an idle's pending interval is the product of the exchanges on its
hosted slots and on the remainder. -/
theorem idle_hosting (i : ℕ) (hi : i < 9) (c : ℕ) (hc : c < 222) :
    exchange ((port (c % 111)).span (7 * idleSource i) (7 * idleTarget i)) =
      ((List.range (copyCount i c)).map fun j =>
          exchange ((port (c % 111)).span (7 * idleSource i + 8 * j)
            (7 * idleSource i + 8 * j + 8))).prod *
        exchange ((port (c % 111)).span (7 * idleSource i + 8 * copyCount i c)
          (7 * idleTarget i)) := by
  have hfit := ((copyCount_fit i hi).2 c hc)
  exact PortCertificate.exchange_slots (port_checked _ (Nat.mod_lt _ (by norm_num))) _ _ _
    (by omega)

/-- The pending interval of an idle is its advance on side zero and on side one. -/
theorem idle_pending (i : ℕ) (hi : i < 9) (t : ℕ) (ht : t < 111) :
    (port t).sourceFrame (idleTarget i) - (port t).sourceFrame (idleSource i) =
        (port t).span (7 * idleSource i) (7 * idleTarget i) ∧
      (port t).targetFrame (idleTarget i) - (port t).targetFrame (idleSource i) =
        (port t).span (7 * idleSource i) (7 * idleTarget i) := by
  have hfit := (copyCount_fit i hi).2 0 (by norm_num)
  exact ⟨PortCertificate.pending_source (port_checked t ht) hfit.1,
    PortCertificate.pending_target (port_checked t ht) hfit.1⟩

/-- The remainder intervals of the idles. -/
def remainderIntervals : List (ℕ × ℕ) :=
  (List.range 9).flatMap fun i => (copyCounts i).map fun k =>
    (7 * idleSource i + 8 * k, 7 * idleTarget i)

theorem remainder_counts_strict : ∀ e ∈ remainderIntervals, e.1 < e.2 ∧ e.2 ≤ 63 ∧
    Fintype.card {p : Pending // (if e.1 ≤ pendingIndex p ∧ pendingIndex p < e.2 then (1 : ℚ)
      else 0) ≠ 0} = e.2 - e.1 := by
  decide +kernel

theorem remainder_counts : ∀ e ∈ remainderIntervals, e.1 ≤ e.2 ∧ e.2 ≤ 63 ∧
    Fintype.card {p : Pending // (if e.1 ≤ pendingIndex p ∧ pendingIndex p < e.2 then (1 : ℚ)
      else 0) ≠ 0} = e.2 - e.1 := by
  intro e he
  obtain ⟨ordered,upper,count⟩ := remainder_counts_strict e he
  exact ⟨ordered.le,upper,count⟩

/-- A remainder child has rank equal to its interval length. -/
theorem rank_remainder (t : ℕ) (ht : t < 111) (e : ℕ × ℕ) (he : e ∈ remainderIntervals) :
    ((port t).span e.1 e.2).rank = e.2 - e.1 := by
  rw [PortCertificate.span, rank_conj _ (PortCertificate.flag_orthonormal (port_checked t ht)),
    interval, Matrix.rank_diagonal]
  exact (remainder_counts e he).2.2

/-- The remainders of the slots are the hosted remainders of the occurrence list. -/
theorem remainders_perm :
    ((List.range 9).flatMap fun i => (copyCounts i).map fun k => (idleRanks 4).getD i 0 - 8 * k).Perm
      remainders := by
  apply perm_of_counts _ _ 43
  · decide +kernel
  · decide +kernel
  · decide +kernel

end IntegerMultBounds.MathlibTM2.M6.BitHosting
