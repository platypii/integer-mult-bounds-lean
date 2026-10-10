import IntegerMultBounds.Machine.FiniteFlowPath
import IntegerMultBounds.Machine.CompactComplexScheduledPCLayout

/-! Fixed-controller paths are composed only at reachable sequence boundaries.
Local contracts are indexed by the actual prefix state, rather than asserted
for every event on every possible caller. Child paths may traverse the same
shared recursive entry and return without rebuilding the transition table. -/
namespace IntegerMultBounds.Machine.CompactComplexScheduledPaths
noncomputable section
open FiniteFlow FiniteFlowPath

/-- Local paths include their real joins, so boundary-to-boundary composition
sums exactly their runtimes and introduces no extra transition. -/
theorem sequence {N t a : ℕ} {states : Fin N → ℕ}
    {family : ∀ pc,Program t (states pc) a} {next : Next states}
    (route : ℕ → Fin N) (banks : ℕ → Tapes t a) (cost : ℕ → ℕ) (count : ℕ)
    (hlocal : ∀ i<count,Path family next (route i) (banks i) (cost i)
      (route (i+1)) (banks (i+1))) :
    Path family next (route 0) (banks 0) (∑ i ∈ Finset.range count,cost i)
      (route count) (banks count) := by
  induction count with
  | zero => simpa only [Finset.sum_range_zero] using Path.nil (route 0) (banks 0)
  | succ count ih =>
    have hp := ih (fun i hi => hlocal i (by omega))
    have hl := hlocal count (by omega)
    simpa only [Finset.sum_range_succ] using FiniteFlowPath.append hp hl

/-- After the last real event the fixed controller reaches its designated
return block; no out-of-range event machine is invoked. -/
def cursor {N count : ℕ} (entries : Fin count → Fin N) (final : Fin N) (i : ℕ) : Fin N :=
  if h : i<count then entries ⟨i,h⟩ else final

private theorem cursor_at {N count : ℕ} (entries : Fin count → Fin N) (final : Fin N)
    (i : Fin count) : cursor entries final i.val=entries i := by
  simp only [cursor,dite_eq_left i.isLt]

private theorem cursor_end {N count : ℕ} (entries : Fin count → Fin N) (final : Fin N) :
    cursor entries final count=final := by
  simp only [cursor,dite_eq_right (Nat.lt_irrefl count)]

/-- Only the exact caller at each reachable event boundary is required by its
local execution proof. Child recursion supplies a path to the next boundary;
all local paths use one fixed family and transition table. -/
theorem sequence_to_final {N t a count : ℕ} {states : Fin N → ℕ}
    {family : ∀ pc,Program t (states pc) a} {next : Next states}
    (entries : Fin count → Fin N) (final : Fin N)
    (banks : ℕ → Tapes t a) (cost : ℕ → ℕ)
    (hlocal : ∀ i : Fin count,Path family next (entries i) (banks i.val) (cost i.val)
      (cursor entries final (i.val+1)) (banks (i.val+1))) :
    Path family next (cursor entries final 0) (banks 0)
      (∑ i ∈ Finset.range count,cost i) final (banks count) := by
  have h := sequence (cursor entries final) banks cost count (fun i hi => by
    have hp := hlocal ⟨i,hi⟩
    rw [cursor_at entries final ⟨i,hi⟩]
    exact hp)
  rw [cursor_end] at h
  exact h

open CompactComplexScheduledPCLayout (eventPC nextPC finalPC)
open CompactComplexCompletedLiveLower (schedule)
attribute [local irreducible] schedule

/-- The actual original event schedule follows its fixed event PCs and reaches
nonleaf return. Each premise concerns only the actual caller at that event's
reachable prefix, including recursive child paths supplied by induction. -/
theorem actual_schedule_path {t a : ℕ} {states : Fin (CompactComplexScheduledPCLayout.originalCount+(4+schedule.length)+2) → ℕ}
    {family : ∀ pc,Program t (states pc) a} {next : Next states}
    (banks : ℕ → Tapes t a) (cost : ℕ → ℕ)
    (hlocal : ∀ i : Fin schedule.length,
      Path family next (eventPC i) (banks i.val) (cost i.val)
        (nextPC i) (banks (i.val+1))) :
    Path family next (cursor eventPC finalPC 0) (banks 0)
      (∑ i ∈ Finset.range schedule.length,cost i) finalPC (banks schedule.length) := by
  apply sequence_to_final eventPC finalPC banks cost
  intro i
  have h := hlocal i
  have hnext : cursor eventPC finalPC (i.val+1)=nextPC i := by
    by_cases hi : i.val+1<schedule.length
    · rw [cursor,dite_eq_left hi,CompactComplexScheduledPCLayout.nextPC_successor i hi]
    · rw [cursor,dite_eq_right hi,CompactComplexScheduledPCLayout.nextPC_final i hi]
  rw [hnext]
  exact h

/-- The same actual node path may be followed by genuine root halting, with
all reachable-event and final trace costs summed on the fixed controller. -/
theorem actual_schedule_then_trace {t a : ℕ} {states : Fin (CompactComplexScheduledPCLayout.originalCount+(4+schedule.length)+2) → ℕ}
    {family : ∀ pc,Program t (states pc) a} {next : Next states}
    (banks : ℕ → Tapes t a) (cost : ℕ → ℕ)
    (hlocal : ∀ i : Fin schedule.length,
      Path family next (eventPC i) (banks i.val) (cost i.val)
        (nextPC i) (banks (i.val+1)))
    {last : Fin (CompactComplexScheduledPCLayout.originalCount+(4+schedule.length)+2)} {m : ℕ} {out : Config t (states last) a}
    (htail : Trace family next finalPC (banks schedule.length) m last out) :
    HoareTime (program family next (cursor eventPC finalPC 0))
      (fun z => z=banks 0) (fun z => z=out.tapes)
      ((∑ i ∈ Finset.range schedule.length,cost i)+m) :=
  path_then_trace_hoare (actual_schedule_path banks cost hlocal) htail

end
end IntegerMultBounds.Machine.CompactComplexScheduledPaths
