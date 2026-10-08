import IntegerMultBounds.Networks.ComplexRank25
import IntegerMultBounds.Networks.BinaryRankFactors
import IntegerMultBounds.Networks.GlobalBinaryResiduals

/-! Actual complex-network edge interfaces in binary tensor coordinates.
The ordered per-edge factorizations count all-column vector factors, not
literal tape instructions. Physical placement and full scheduled composition
are separate from these exact edge operator identities. -/

namespace IntegerMultBounds.Networks.ComplexPhaseBudget

open ComplexRank25

abbrev Label := Submodule (ZMod 2) (Labels.Cube (ZMod 2) 25)

noncomputable def updates :=
  GlobalProjectionRank.trace (Labels.binary 25) form_symm Labels.binary_nondegenerate
    vector vector_self triples pairs (Equiv.refl (Fin 26)) owner gather inject scatter wires

noncomputable def edges : List (Label × Label) :=
  RankTrace.edges (GlobalLabels.source vector) updates

abbrev form := GlobalProjectionRank.cubeForm (Labels.binary 25)
abbrev formSymm : form.IsSymm := GlobalProjectionRank.cube_symm (Labels.binary 25) form_symm
abbrev coordinateSymm : (Labels.binary (25 ^ 3)).IsSymm := ⟨Labels.form_symm 0⟩

/-- Both labels on every actual sequential edge are nondegenerate. -/
theorem edges_nondegenerate : ∀ p ∈ edges,
    (form.restrict p.1).Nondegenerate ∧ (form.restrict p.2).Nondegenerate :=
  ProjectionTrace.edges_predicate (fun U : Label => (form.restrict U).Nondegenerate)
    (GlobalLabels.source vector) updates
    (GlobalProjectionRank.source_nondegenerate (Labels.binary 25) vector vector_self)
    (GlobalProjectionRank.trace_nondegenerate (Labels.binary 25) form_symm Labels.binary_nondegenerate
      vector vector_self triples pairs (Equiv.refl (Fin 26)) owner gather inject scatter wires)

/-- The same physical edges used by the established finite-network rank theorem. -/
theorem rank_sum_eq :
    (edges.map (fun p => ProjectionTrace.edgeRank form formSymm p.1 p.2)).sum = rankSum := rfl

/-- Every physical edge has the concrete residual witness needed by the
binary kernel construction, including skipped labels and terminal edges. -/
theorem edges_residuals : ∀ p ∈ edges,
    (p.1 ≤ p.2 ∧ BinaryMotifResiduals.Good form (ProjectionRank.residual form p.1 p.2)) ∨
    (p.2 ≤ p.1 ∧ BinaryMotifResiduals.Good form (ProjectionRank.residual form p.2 p.1)) := by
  have heven (p : Fin (Fintype.card (NeighborCounts.ComplexPairs 25))) :
      Even ((triples (owner p)).val ∩ (triples (target p)).val).card := by
    rw [Finset.inter_comm]
    exact (GlobalCircuit.complexLocalPairs triples pairs p).property.2
  exact GlobalBinaryResiduals.network_residuals (fun T : NeighborCounts.Triple 25 => T.val)
    (fun T => T.property) (by norm_num) triples pairs (Equiv.refl (Fin 26))
    owner gather inject scatter target inject_support heven wires

/-- Each list realizes its corresponding physical edge's coordinate-label
operator, simultaneously for every number of columns. -/
def Realizes (factors : List (List (ZMod 4 × BinaryWalsh.Address (25 ^ 3)))) : Prop :=
  List.Forall₂ (fun p gs =>
    (∀ g ∈ gs, g.1 = 1 ∨ g.1 = -1) ∧
    ∀ k, BinaryRankFactors.edgeOperator coordinateSymm k
      (LabelTransport.label (TensorCoordinates.coordinates 25) p.1)
      (LabelTransport.label (TensorCoordinates.coordinates 25) p.2) =
        (gs.map (BinaryColumns.vectorFactor k)).prod) edges factors

/-- A single finite family of kernel directions realizes all actual edge
interfaces for every column count, with exactly the proved rank total. -/
theorem exists_uniform_factors :
    ∃ factors : List (List (ZMod 4 × BinaryWalsh.Address (25 ^ 3))),
      Realizes factors ∧ (factors.map List.length).sum = rankSum := by
  obtain ⟨factors, hop, hlen⟩ := BinaryRankFactors.exists_uniform_list_transport_factors
    form formSymm coordinateSymm (TensorCoordinates.coordinates 25)
    (TensorCoordinates.coordinates_isometry 25) edges edges_nondegenerate edges_residuals
  exact ⟨factors, hop, hlen.trans rank_sum_eq⟩

/-- The actual edge factors meet the finite complex-network budget and
branching exponent. Counts are vector factors, with physical tape cost open. -/
theorem exists_uniform_factor_budget :
    ∃ factors : List (List (ZMod 4 × BinaryWalsh.Address (25 ^ 3))),
      Realizes factors ∧ (factors.map List.length).sum ≤ 916333630984500000 ∧
      ((factors.map List.length).sum : ℝ) / 58645352620000 <
        (15625 : ℝ) ^ Parameters.sigma := by
  obtain ⟨factors, hop, hlen⟩ := exists_uniform_factors
  exact ⟨factors, hop, hlen ▸ rank_budget, hlen ▸ branching_bound⟩

end IntegerMultBounds.Networks.ComplexPhaseBudget
