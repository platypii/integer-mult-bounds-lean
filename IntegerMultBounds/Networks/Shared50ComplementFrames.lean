import IntegerMultBounds.Networks.Shared50Frames
import IntegerMultBounds.Networks.DAGComplementExecution

/-! Complementary reverse frames of the actual shared fifty-copy DAG.
Ambient nondegeneracy and common-point support premises are discharged.
These are middle-computation traces, without surrounding motif/sink joins. -/

namespace IntegerMultBounds.Networks.Shared50ComplementFrames

open NeighborCounts SharedPointReplay

attribute [local irreducible] SharedPointReplay.circuit

abbrev triples : Triple 50 → Finset (Fin 50) := fun T => T.val

def input := DAGComplementTrace.reverseInput circuit.nodes outputRefs triples
def output := DAGComplementTrace.reverseOutput circuit.nodes outputRefs triples
def updates := DAGComplementTrace.reverseTrace circuit.nodes outputRefs triples

theorem endpoints : RankTrace.finish input updates = output :=
  DAGComplementTrace.reverse_endpoints circuit.nodes outputRefs triples

theorem increasing : ∀ p ∈ RankTrace.edges input updates, p.1 ≤ p.2 :=
  DAGComplementTrace.reverse_increasing circuit.nodes outputRefs valid outputRefs_bounds triples

theorem loss_zero : RankTrace.loss (fun U : Submodule ℚ (Fin 50 → ℚ) => Module.finrank ℚ U)
    input updates = 0 :=
  DAGComplementTrace.reverse_loss_zero circuit.nodes outputRefs valid outputRefs_bounds triples

theorem nondegenerate : ∀ p ∈ RankTrace.edges input updates,
    ((Labels.rational 50).restrict p.1).Nondegenerate ∧
      ((Labels.rational 50).restrict p.2).Nondegenerate :=
  DAGComplementTrace.reverse_nondegenerate circuit.nodes outputRefs valid outputRefs_bounds triples
    (by decide) Shared50Frames.node_common

/-- Complemented initial frames are computed from the actual forward terminal
label, so every target attachment uses its verified partial-output span. -/
theorem input_at_output (c : Fin 50) (j : Fin 1176) :
    input (SharedPointExecution.code.outputSlot (SharedPointOutputIndex.index c j)) =
      (Labels.rational 50).orthogonal (SharedPointMap.outputSpan c (embedding c j)) := by
  change (Labels.rational 50).orthogonal
    (Shared50Frames.finalLabels (SharedPointExecution.code.outputSlot (SharedPointOutputIndex.index c j))) = _
  rw [Shared50Frames.final_label]

/-- The actual reversed computation accepts the physical target line inside
its complemented partial-output label. -/
theorem target_le_input (c : Fin 50) (j : Fin 1176) :
    (ℚ ∙ (Labels.indicator (embedding c j).val : Fin 50 → ℚ)) ≤
      input (SharedPointExecution.code.outputSlot (SharedPointOutputIndex.index c j)) := by
  rw [input_at_output]
  apply SharedPointMap.target_le_outputSpan_orthogonal
  change c ∈ (SharedPointLift.source (SharedPointLift.pairPayload 49)
    (SharedPointLift.pairPayload_card 49) c j).val
  rw [SharedPointLift.source_val (SharedPointLift.pairPayload 49) (SharedPointLift.pairPayload_card 49) c j]
  exact Finset.mem_insert_self _ _

/-- Reverse terminal labels are exactly orthogonal complements of the actual
initial source-span labels (hence full on initially empty scratch). -/
theorem output_eq (i : ℕ) : output i = (Labels.rational 50).orthogonal (Shared50Frames.initialLabels i) := rfl

end IntegerMultBounds.Networks.Shared50ComplementFrames
