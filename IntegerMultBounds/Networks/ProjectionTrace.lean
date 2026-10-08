import IntegerMultBounds.Networks.RankTrace

/-! Genuine projection-rank accounting on traces whose labels are ordinary
submodules. Nondegeneracy is proved for actual endpoints by a trace invariant;
it is not encoded into a replacement trace or an assigned edge cost. -/

namespace IntegerMultBounds.Networks.ProjectionTrace

open Module

section Invariants
variable {ι L : Type*} [DecidableEq ι]

/-- Updating a register by a label satisfying a predicate preserves that
predicate at every register. -/
theorem update_predicate (P : L → Prop) (current : ι → L) (i : ι) (next : L)
    (hc : ∀ j, P (current j)) (hn : P next) :
    ∀ j, P (Function.update current i next j) := by
  intro j
  by_cases hj : j = i
  · subst j; simpa using hn
  · simpa [Function.update_of_ne hj] using hc j

/-- The final actual label of every register satisfies the invariant. -/
theorem finish_predicate (P : L → Prop) (current : ι → L) (updates : List (ι × L))
    (hc : ∀ i, P (current i)) (hu : ∀ u ∈ updates, P u.2) :
    ∀ i, P (RankTrace.finish current updates i) := by
  induction updates generalizing current with
  | nil => exact hc
  | cons u rest ih =>
    rcases u with ⟨i, next⟩
    exact ih (Function.update current i next)
      (update_predicate P current i next hc (hu (i, next) (by simp)))
      (fun u hu' => hu u (by simp [hu']))

/-- Both endpoints of every actual sequential trace edge satisfy the invariant,
including repeated occurrences of one physical wire in the same group. -/
theorem edges_predicate (P : L → Prop) (current : ι → L) (updates : List (ι × L))
    (hc : ∀ i, P (current i)) (hu : ∀ u ∈ updates, P u.2) :
    ∀ e ∈ RankTrace.edges current updates, P e.1 ∧ P e.2 := by
  induction updates generalizing current with
  | nil => simp [RankTrace.edges]
  | cons u rest ih =>
    rcases u with ⟨i, next⟩
    intro e he
    simp only [RankTrace.edges, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨hc i, hu (i, next) (by simp)⟩
    · exact ih (Function.update current i next)
        (update_predicate P current i next hc (hu (i, next) (by simp)))
        (fun u hu' => hu u (by simp [hu'])) e he
end Invariants

section Projections
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (B : LinearMap.BilinForm K E) (hs : B.IsSymm)

/-- A total projector API on raw submodule labels. On every label used by a
verified trace, the nondegenerate branch is selected and is the actual
orthogonal projection; the fallback makes no claim on degenerate labels. -/
noncomputable def projector (U : Submodule K E) : E →ₗ[K] E := by
  classical
  exact if hu : (B.restrict U).Nondegenerate then ProjectionRank.project B hs U hu else 0

@[simp] theorem projector_eq (U : Submodule K E) (hu : (B.restrict U).Nondegenerate) :
    projector B hs U = ProjectionRank.project B hs U hu := by
  simp only [projector, dite_eq_left hu]

/-- An edge's cost is the rank of its genuine projector difference. -/
noncomputable def edgeRank (U V : Submodule K E) : ℕ :=
  finrank K (LinearMap.range (projector B hs V - projector B hs U))

theorem edgeRank_eq (U V : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) (hv : (B.restrict V).Nondegenerate)
    (hc : U ≤ V ∨ V ≤ U) :
    edgeRank B hs U V = (finrank K V - finrank K U) + (finrank K U - finrank K V) := by
  have he : edgeRank B hs U V =
      RankTrace.edgeRank B hs ⟨U, hu⟩ ⟨V, hv⟩ := by
    unfold edgeRank RankTrace.edgeRank
    rw [projector_eq B hs U hu, projector_eq B hs V hv]
  rw [he]
  exact RankTrace.edgeRank_eq B hs ⟨U, hu⟩ ⟨V, hv⟩ hc

/-- Total actual operator rank across the supplied sequential submodule trace. -/
noncomputable def rankSum {ι : Type*} [DecidableEq ι]
    (current : ι → Submodule K E) (updates : List (ι × Submodule K E)) : ℕ :=
  ((RankTrace.edges current updates).map fun e => edgeRank B hs e.1 e.2).sum

/-- Every checked edge contributes its proved dimension variation, derived
from projection ranges rather than defined as a dimension charge. -/
theorem rankSum_eq_variation {ι : Type*} [DecidableEq ι]
    (current : ι → Submodule K E) (updates : List (ι × Submodule K E))
    (hcurrent : ∀ i, (B.restrict (current i)).Nondegenerate)
    (hupdates : ∀ u ∈ updates, (B.restrict u.2).Nondegenerate)
    (hcomparable : ∀ e ∈ RankTrace.edges current updates, e.1 ≤ e.2 ∨ e.2 ≤ e.1) :
    rankSum B hs current updates = RankTrace.variation (fun U : Submodule K E => finrank K U) current updates := by
  unfold rankSum RankTrace.variation
  congr 1
  apply List.map_congr_left
  intro e he
  obtain ⟨hu, hv⟩ := edges_predicate (fun U : Submodule K E => (B.restrict U).Nondegenerate)
    current updates hcurrent hupdates e he
  exact edgeRank_eq B hs e.1 e.2 hu hv (hcomparable e he)

/-- Exact telescoping balance for the sum of actual projection-difference
ranks on a concrete raw-submodule trace. Endpoint dimensions and downward
variation refer to that same physical update history. -/
theorem rank_balance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (current : ι → Submodule K E) (updates : List (ι × Submodule K E))
    (hcurrent : ∀ i, (B.restrict (current i)).Nondegenerate)
    (hupdates : ∀ u ∈ updates, (B.restrict u.2).Nondegenerate)
    (hcomparable : ∀ e ∈ RankTrace.edges current updates, e.1 ≤ e.2 ∨ e.2 ≤ e.1) :
    rankSum B hs current updates + RankTrace.total (fun U : Submodule K E => finrank K U) current =
      RankTrace.total (fun U : Submodule K E => finrank K U) (RankTrace.finish current updates) +
        2 * RankTrace.loss (fun U : Submodule K E => finrank K U) current updates := by
  rw [rankSum_eq_variation B hs current updates hcurrent hupdates hcomparable]
  exact RankTrace.variation_balance _ current updates
end Projections
end IntegerMultBounds.Networks.ProjectionTrace
