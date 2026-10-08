import IntegerMultBounds.Networks.FramedEdgeTrace
import IntegerMultBounds.Networks.Shared50FiniteFramed
import IntegerMultBounds.Networks.Shared50FiniteReverseTrace

/-! The physical frame pairs of the actual finite fifty-copy program agree
exactly, in order and with repetitions, with the proved forward and complementary
reverse rank traces. -/

namespace IntegerMultBounds.Networks.Shared50PhysicalEdges

open FramedCircuit FramedEdgeTrace DAGSupportTrace

section Generic
variable {α E : Type*} {h : ℕ} [AddCommGroup E] [Module (ZMod 2) E]

theorem forward_event (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (current : ℕ → Finset α) (event : Event α) :
    pairs (DAGFramedExecution.eventInstructions triples frameOf current event) =
      (RankTrace.edges (fun i => FanoutFrames.label triples (current i)) (event.updates triples)).map
        (fun p => (frameOf p.1,frameOf p.2)) := by
  rw [DAGFramedExecution.eventInstructions,pairs_append,pairs_gates,List.append_nil]
  exact pairs_edges frameOf _ (fun _ => FanoutFrames.label triples event.support) _

theorem forward_schedule (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (es : List (Event α)) (current : ℕ → Finset α) :
    pairs (DAGFramedExecution.schedule triples frameOf es current) =
      (RankTrace.edges (fun i => FanoutFrames.label triples (current i)) (updates es triples)).map
        (fun p => (frameOf p.1,frameOf p.2)) := by
  induction es generalizing current with
  | nil => rfl
  | cons event es ih =>
    rw [DAGFramedExecution.schedule,pairs_append,forward_event,ih]
    simp only [updates,List.flatMap_cons,RankTrace.edges_append,List.map_append]
    rw [← event.after_labels]

theorem align_pairs {L : Type*} (frameOf : L → Frame (ZMod 2) E)
    (current : ℕ → L) (xs : List (ℕ × L)) :
    pairs (DAGComplementExecution.align frameOf current xs) =
      (RankTrace.edges current xs).map (fun p => (frameOf p.1,frameOf p.2)) := by
  induction xs generalizing current with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨i,next⟩ := p
    simp only [DAGComplementExecution.align,pairs,List.filterMap_cons,RankTrace.edges,List.map_cons]
    exact congrArg (List.cons _) (ih _)

theorem inverse_trace_finish (triples : α → Finset (Fin h))
    (es : List (Event α)) (current : ℕ → Finset α) :
    RankTrace.finish (DAGComplementExecution.dualLabels triples (DAGSupportTrace.run es current))
      (DAGComplementExecution.trace triples es current) = DAGComplementExecution.dualLabels triples current := by
  have he : DAGComplementExecution.dualLabels triples (DAGSupportTrace.run es current) =
      fun i => (Labels.rational h).orthogonal
        (RankTrace.finish (fun j => FanoutFrames.label triples (current j)) (updates es triples) i) := by
    funext i
    exact congrArg (Labels.rational h).orthogonal (congrFun (run_labels es triples current) i)
  rw [he,DAGComplementExecution.trace_eq_undo,DAGComplementTrace.undo_finish]
  rfl

theorem inverse_event (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (current : ℕ → Finset α) (event : Event α) :
    pairs (DAGComplementExecution.eventInverse triples frameOf current event) =
      (RankTrace.edges (DAGComplementExecution.dualLabels triples (event.after current))
        (DAGComplementExecution.eventUndo event triples current)).map
        (fun p => (frameOf p.1,frameOf p.2)) := by
  rw [DAGComplementExecution.eventInverse,pairs_append,pairs_gates,List.nil_append,align_pairs]

theorem inverse_schedule (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (es : List (Event α)) (current : ℕ → Finset α) :
    pairs (DAGComplementExecution.schedule triples frameOf es current) =
      (RankTrace.edges (DAGComplementExecution.dualLabels triples (DAGSupportTrace.run es current))
        (DAGComplementExecution.trace triples es current)).map
        (fun p => (frameOf p.1,frameOf p.2)) := by
  induction es generalizing current with
  | nil => rfl
  | cons event es ih =>
    rw [DAGComplementExecution.schedule,pairs_append,ih,inverse_event]
    simp only [DAGComplementExecution.trace,DAGSupportTrace.run,RankTrace.edges_append,List.map_append]
    rw [inverse_trace_finish]

end Generic

open NeighborCounts SharedPointReplay
attribute [local irreducible] circuit
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- Exact ordered frame pairs of the bounded physical forward program. -/
theorem forward (frameOf : Submodule ℚ (Fin 50 → ℚ) → Frame (ZMod 2) E) :
    pairs (Shared50FiniteFramed.forward frameOf) =
      (RankTrace.edges Shared50Frames.initialLabels Shared50Frames.updates).map
        (fun p => (frameOf p.1,frameOf p.2)) := by
  rw [Shared50FiniteFramed.forward,pairs_restrict]
  exact forward_schedule (fun T : Triple 50 => T.val) frameOf _ _

/-- Exact ordered frame pairs of the bounded physical complementary inverse. -/
theorem inverse (frameOf : Submodule ℚ (Fin 50 → ℚ) → Frame (ZMod 2) E) :
    pairs (Shared50FiniteFramed.inverse frameOf) =
      (RankTrace.edges Shared50ComplementFrames.input Shared50ComplementFrames.updates).map
        (fun p => (frameOf p.1,frameOf p.2)) := by
  rw [Shared50FiniteFramed.inverse,pairs_restrict]
  rw [DAGComplementExecution.inverse,inverse_schedule,DAGComplementExecution.inverse_trace]
  congr 2
  funext i
  exact congrArg (Labels.rational 50).orthogonal
    (congrFun (run_labels (events circuit.nodes outputRefs) (fun T : Triple 50 => T.val)
      (initialSupports circuit.nodes outputRefs)) i)

/-- The same exact forward edge list expressed entirely on the finite bank. -/
theorem forward_finite (frameOf : Submodule ℚ (Fin 50 → ℚ) → Frame (ZMod 2) E) :
    pairs (Shared50FiniteFramed.forward frameOf) =
      RankTrace.edges (fun i : Fin 509194 => frameOf (Shared50Frames.initialLabels i.val))
        (Shared50FiniteTrace.forward frameOf) := by
  rw [forward,Shared50FiniteTrace.forward_edges]

/-- The same exact reverse edge list expressed entirely on the finite bank. -/
theorem inverse_finite (frameOf : Submodule ℚ (Fin 50 → ℚ) → Frame (ZMod 2) E) :
    pairs (Shared50FiniteFramed.inverse frameOf) =
      RankTrace.edges (fun i : Fin 509194 => frameOf (Shared50ComplementFrames.input i.val))
        (Shared50FiniteReverseTrace.reverse frameOf) := by
  rw [inverse,Shared50FiniteReverseTrace.reverse_edges]

end IntegerMultBounds.Networks.Shared50PhysicalEdges
