module

public import IntegerMultBounds.MathlibTM2.Routing.PermutationMatchings

/-! A bounded running-minimum scan computes the existing canonical cycle base.
This is the semantic invariant for executed lookup/minimum loops. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
variable {ι : Type*} [LinearOrder ι]

def permutationOrbitMinimum (f : ι → ι) (query : ι) : ℕ → ι
  | 0 => query
  | n + 1 => min ((f^[n + 1]) query) (permutationOrbitMinimum f query n)

theorem permutationOrbitMinimum_le_iterate (f : ι → ι) (query : ι) (n k : ℕ) (hk : k ≤ n) :
    permutationOrbitMinimum f query n ≤ (f^[k]) query := by
  induction n with
  | zero =>
      have he : k = 0 := by omega
      subst k
      exact le_rfl
  | succ n ih =>
      by_cases he : k = n + 1
      · subst k; exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih (by omega))

theorem permutationOrbitMinimum_is_iterate (f : ι → ι) (query : ι) (n : ℕ) :
    ∃ k ≤ n, permutationOrbitMinimum f query n = (f^[k]) query := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
      obtain ⟨k, hk, he⟩ := ih
      by_cases h : (f^[n + 1]) query ≤ permutationOrbitMinimum f query n
      · exact ⟨n + 1, le_rfl, min_eq_left h⟩
      · exact ⟨k, by omega, (min_eq_right (le_of_not_ge h)).trans he⟩

/-- One full coordinate count suffices, including fixed points and short cycles. -/
theorem permutationOrbitMinimum_eq_base [Fintype ι] [DecidableEq ι]
    (f : Equiv.Perm ι) (query : ι) :
    permutationOrbitMinimum f query (Fintype.card ι) = permutationBase f query := by
  apply le_antisymm
  · have hbase := Finset.min'_mem (permutationOrbit f query) (permutationOrbit_nonempty f query)
    obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hbase).2
    have hle := permutationOrbitMinimum_le_iterate (f : ι → ι) query (Fintype.card ι) k.val
      (Nat.le_of_lt k.isLt)
    have he : (f^[k.val]) query = permutationBase f query := by
      simpa only [Equiv.Perm.coe_pow, permutationBase] using hk
    exact hle.trans_eq he
  · obtain ⟨k, _, hk⟩ := permutationOrbitMinimum_is_iterate (f : ι → ι) query (Fintype.card ι)
    apply Finset.min'_le (permutationOrbit f query) _
    apply (mem_permutationOrbit f query _).mpr
    rw [hk]
    exact ⟨k, rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
