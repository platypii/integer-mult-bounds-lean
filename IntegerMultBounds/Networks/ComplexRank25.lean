import IntegerMultBounds.Networks.GlobalProjectionRank
import IntegerMultBounds.Networks.MotifSupport

/-! The actual h=25 complex network's projection-rank budget. All labels,
coefficients, physical incidences and terminal dimensions are instantiated;
no trace-balance or rank-loss estimate is an assumption. This is a finite
network rank theorem, not yet a phase-interface or tape-runtime theorem. -/

namespace IntegerMultBounds.Networks.ComplexRank25

open Module NeighborCounts

noncomputable def triples : Fin 2300 ≃ Triple 25 :=
  (Fintype.equivFinOfCardEq (by rw [triple_card]; decide)).symm

noncomputable def pairs : Fin (Fintype.card (ComplexPairs 25)) ≃ ComplexPairs 25 :=
  (Fintype.equivFin _).symm

abbrev vector (T : Triple 25) : Fin 25 → ZMod 2 := Labels.indicator T.val

theorem form_symm : (Labels.binary 25).IsSymm :=
  ⟨Labels.form_symm 0⟩

theorem vector_self (T : Triple 25) : Labels.binary 25 (vector T) (vector T) ≠ 0 := by
  rw [vector, Labels.binary_self T.val T.property]
  exact one_ne_zero

noncomputable def owner (p : Fin (Fintype.card (ComplexPairs 25))) : Fin 2300 :=
  (GlobalCircuit.complexLocalPairs triples pairs p).val.2

noncomputable def target (p : Fin (Fintype.card (ComplexPairs 25))) : Fin 2300 :=
  (GlobalCircuit.complexLocalPairs triples pairs p).val.1

noncomputable def gather := Circuit.complexGather (fun i => (triples i).val)
noncomputable def inject := Circuit.complexInject (GlobalCircuit.complexLocalPairs triples pairs)
noncomputable def scatter := Circuit.complexScatter (fun i => (triples i).val)

theorem inject_support (i : Fin 2300) (p : Fin (Fintype.card (ComplexPairs 25))) :
    inject i p ≠ 0 ↔ target p = i :=
  MotifSupport.complexInject_ne_zero _ i p

theorem neighbor_orthogonal (p : Fin (Fintype.card (ComplexPairs 25))) :
    Labels.binary 25 (vector (triples (owner p))) (vector (triples (target p))) = 0 := by
  apply Labels.binary_neighbors
  rw [Finset.inter_comm]
  exact (GlobalCircuit.complexLocalPairs triples pairs p).property.2

/-- The same labeled physical circuit whose erasure is GlobalGrouped.complexProgram. -/
noncomputable def program :=
  GlobalLabels.program (Labels.binary 25) form_symm Labels.binary_nondegenerate vector vector_self
    triples pairs (Equiv.refl (Fin 26)) owner gather inject scatter

theorem program_groups : program.map GroupedFrames.Vertex.group =
    GlobalGrouped.complexProgram triples pairs :=
  GlobalLabels.program_groups _ _ _ _ _ _ _ _ _ _ _ _

/-- Every physical wire appears once in the terminal-alignment list. -/
noncomputable def wires : List (Wires.ComplexRole 25) :=
  List.ofFn (Fintype.equivFin (Wires.ComplexRole 25)).symm

theorem wires_complete (i : Wires.ComplexRole 25) : i ∈ wires := by
  apply List.mem_ofFn.mpr
  exact ⟨(Fintype.equivFin _ ) i, (Fintype.equivFin _).symm_apply_apply i⟩

noncomputable def rankSum : ℕ :=
  GlobalProjectionRank.rankSum (Labels.binary 25) form_symm Labels.binary_nondegenerate
    vector vector_self triples pairs (Equiv.refl (Fin 26)) owner gather inject scatter wires

/-- The actual sum of projector-difference ranks satisfies the selected finite
complex-network budget, without a supplied balance or loss hypothesis. -/
theorem rank_budget : rankSum ≤ 916333630984500000 := by
  have hh := GlobalProjectionRank.rank_le_dimensions (Labels.binary 25) form_symm
    Labels.binary_nondegenerate vector vector_self triples pairs (Equiv.refl (Fin 26))
    owner gather inject scatter target inject_support neighbor_orthogonal wires wires_complete
  have hw : Fintype.card (GlobalCircuit.World (Triple 25) (ComplexPairs 25) (Fin 26)) =
      58645352620000 := NetworkBudget.complex_role_card_25
  rw [hw, triple_card, show Nat.choose 25 3 = 2300 by decide] at hh
  norm_num at hh ⊢
  exact hh

/-- The actual finite network meets the chosen complex branching exponent. -/
theorem branching_bound :
    (rankSum : ℝ) / 58645352620000 < (15625 : ℝ) ^ Parameters.sigma := by
  have hr : (rankSum : ℝ) ≤ 916333630984500000 := by exact_mod_cast rank_budget
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right hr (by norm_num))
    Parameters.complex_branching_bound

end IntegerMultBounds.Networks.ComplexRank25
