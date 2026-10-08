import IntegerMultBounds.Networks.Shared50FiniteTrace

/-! The exact complementary reverse stage trace on the certified finite bank.
All reversed frame incidences are retained, with the same endpoint labels and
ordered edges as the actual natural-register complementary schedule. -/

namespace IntegerMultBounds.Networks.Shared50FiniteReverseTrace

open Shared50FiniteTrace

/-- Undoing a bounded trace introduces no new physical role. -/
theorem bounded_undo {L M : Type*} (capacity : ℕ) (dual : L → M) (current : ℕ → L)
    (xs : List (ℕ × L)) (hb : bounded capacity xs) :
    bounded capacity (DAGComplementTrace.undo dual current xs) := by
  induction xs generalizing current with
  | nil => simp [DAGComplementTrace.undo, bounded]
  | cons p xs ih =>
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ih (Function.update current p.1 p.2) (fun r hr => hb r (by simp [hr])) q hq
    · have he : q = (p.1, dual (current p.1)) := by simpa using hq
      subst q
      exact hb p (by simp)

theorem reverse_bound : bounded 509194 Shared50ComplementFrames.updates :=
  bounded_undo 509194 (Labels.rational 50).orthogonal Shared50Frames.initialLabels
    Shared50Frames.updates forward_bound

theorem stage_bound {L : Type*} (f : Submodule ℚ (Fin 50 → ℚ) → L) :
    bounded 509194 (Shared50StageFrames.mapUpdates f Shared50ComplementFrames.updates) :=
  bounded_map _ _ reverse_bound f

/-- Actual finite complementary reverse trace after a chosen stage label lift. -/
def reverse {L : Type*} (f : Submodule ℚ (Fin 50 → ℚ) → L) : List (Fin 509194 × L) :=
  restrictUpdates 509194 (Shared50StageFrames.mapUpdates f Shared50ComplementFrames.updates) (stage_bound f)

theorem reverse_finish {L : Type*} (f : Submodule ℚ (Fin 50 → ℚ) → L) :
    RankTrace.finish (fun i : Fin 509194 => f (Shared50ComplementFrames.input i.val)) (reverse f) =
      fun i => f (Shared50ComplementFrames.output i.val) := by
  rw [reverse, finish_restrict _ _ _ (fun i => f (Shared50ComplementFrames.input i))]
  have hh := Shared50StageFrames.finish_map f Shared50ComplementFrames.input Shared50ComplementFrames.updates
  rw [Shared50ComplementFrames.endpoints] at hh
  exact congrArg (fun g => fun i : Fin 509194 => g i.val) hh

theorem reverse_edges {L : Type*} (f : Submodule ℚ (Fin 50 → ℚ) → L) :
    RankTrace.edges (fun i : Fin 509194 => f (Shared50ComplementFrames.input i.val)) (reverse f) =
      (RankTrace.edges Shared50ComplementFrames.input Shared50ComplementFrames.updates).map
        (fun p => (f p.1,f p.2)) := by
  rw [reverse, edges_restrict _ _ _ (fun i => f (Shared50ComplementFrames.input i)),
    Shared50StageFrames.edges_map]

end IntegerMultBounds.Networks.Shared50FiniteReverseTrace
