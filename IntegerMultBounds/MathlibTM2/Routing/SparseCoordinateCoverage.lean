module

public import IntegerMultBounds.MathlibTM2.Routing.SparseCoordinateRuns

/-! Dense expansion of coordinate-generated runs covers exactly the interval
from the initial cursor through the last target, including every gap. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {W : ℕ}

theorem sparseCoordinateEnd_ge (L cursor : ℕ) (entries : List (ℕ × ℕ))
    (hr : SparseCoordinatesReady L cursor entries) : cursor ≤ sparseCoordinateEnd cursor entries := by
  induction entries generalizing cursor with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    obtain ⟨_, hyx, ht⟩ := hr
    have he := ih (x + 1) ht
    change cursor ≤ sparseCoordinateEnd (x + 1) rest
    omega

theorem sparseCoordinateRuns_coverage (L cursor : ℕ) (entries : List (ℕ × Fin (W + 1)))
    (hr : SparseCoordinatesReady L cursor (sparseCoordinateValues entries)) :
    (SparseSelectorRun.expand (sparseCoordinateRuns cursor entries)).length =
      sparseCoordinateEnd cursor (sparseCoordinateValues entries) - cursor := by
  induction entries generalizing cursor with
  | nil => simp [sparseCoordinateRuns, SparseSelectorRun.expand, sparseCoordinateValues, sparseCoordinateEnd]
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    obtain ⟨hx, hyx, ht⟩ := hr
    have hh := ih (x + 1) ht
    have he := sparseCoordinateEnd_ge L (x + 1) (sparseCoordinateValues rest) ht
    simp only [sparseCoordinateRuns, SparseSelectorRun.expand, SparseSelectorRun.indices,
      List.length_append, List.length_replicate, List.length_singleton] at ⊢
    rw [hh]
    change x - cursor + 1 + (sparseCoordinateEnd (x + 1) (sparseCoordinateValues rest) - (x + 1)) =
      sparseCoordinateEnd (x + 1) (sparseCoordinateValues rest) - cursor
    omega

/-- Gaps and live entries partition the traversed coordinate interval. -/
theorem sparseCoordinateRuns_gap_sum (L cursor : ℕ)
    (entries : List (ℕ × Fin (W + 1)))
    (hr : SparseCoordinatesReady L cursor (sparseCoordinateValues entries)) :
    ((sparseCoordinateRuns cursor entries).map (fun run => run.gap)).sum +
      entries.length = sparseCoordinateEnd cursor (sparseCoordinateValues entries) - cursor := by
  induction entries generalizing cursor with
  | nil => simp [sparseCoordinateRuns, sparseCoordinateValues, sparseCoordinateEnd]
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    obtain ⟨_, hyx, ht⟩ := hr
    have hh := ih (x + 1) ht
    have he := sparseCoordinateEnd_ge L (x + 1) (sparseCoordinateValues rest) ht
    simp only [sparseCoordinateRuns, List.map_cons, List.sum_cons, List.length_cons]
    change x - cursor + _ + (rest.length + 1) =
      sparseCoordinateEnd (x + 1) (sparseCoordinateValues rest) - cursor
    omega

/-- Emitting a zero selector at the final physical position closes the suffix. -/
theorem sparseCoordinateEnd_append (cursor : ℕ) (entries rest : List (ℕ × ℕ)) :
    sparseCoordinateEnd cursor (entries ++ rest) =
      sparseCoordinateEnd (sparseCoordinateEnd cursor entries) rest := by
  induction entries generalizing cursor with
  | nil => rfl
  | cons pair entries ih => cases pair; exact ih _

theorem sparseCoordinateEnd_terminal (cursor last : ℕ) (entries : List (ℕ × ℕ)) :
    sparseCoordinateEnd cursor (entries ++ [(last, 0)]) = last + 1 := by
  rw [sparseCoordinateEnd_append]
  rfl

end IntegerMultBounds.MathlibTM2.Routing
