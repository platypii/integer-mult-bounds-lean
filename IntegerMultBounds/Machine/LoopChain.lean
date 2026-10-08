import IntegerMultBounds.Machine.Loop

/-! A while loop whose iterations are a chain of exact-tape contracts: the
`j`-th iteration carries bank `j` to bank `j + 1` within its own bound, every
bank before the last passes the local test, and the last fails it. The loop
then carries bank zero to the last bank within the sum of the iteration
bounds plus two control transitions per iteration. -/

namespace IntegerMultBounds.Machine

variable {t q a : ℕ}

theorem while_chain_run (M : Program t q a) (test : (Fin t → Fin (a + 4)) → Bool)
    (X : ℕ → Tapes t a) (cost : ℕ → ℕ) (n : ℕ)
    (hbody : ∀ j < n, HoareTime M (fun v => v = X j) (fun v => v = X (j + 1)) (cost j))
    (htest : ∀ j < n, test (X j).reads = true) :
    ∃ k ≤ ∑ j ∈ Finset.range n, (cost j + 2),
      run (whileLoop M test) k ((X 0).start (whileLoop M test)) =
        some ((X n).start (whileLoop M test)) := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
    obtain ⟨k, hk, hr⟩ := ih (fun j hj => hbody j (by omega)) (fun j hj => htest j (by omega))
    obtain ⟨k', c, hk', hr', hh, hc⟩ := hbody n (by omega) (X n) rfl
    refine ⟨k + (k' + 2), ?_, ?_⟩
    · rw [Finset.sum_range_succ]; omega
    · rw [run_add, hr]
      simp only [Option.bind_some]
      rw [while_run_iteration M test (X n) (htest n (by omega)) hr' hh, hc]

/-- The chained loop contract. -/
theorem while_chain_hoare (M : Program t q a) (test : (Fin t → Fin (a + 4)) → Bool)
    (X : ℕ → Tapes t a) (cost : ℕ → ℕ) (n : ℕ)
    (hbody : ∀ j < n, HoareTime M (fun v => v = X j) (fun v => v = X (j + 1)) (cost j))
    (htest : ∀ j < n, test (X j).reads = true) (hexit : test (X n).reads = false) :
    HoareTime (whileLoop M test) (fun v => v = X 0) (fun v => v = X n)
      (∑ j ∈ Finset.range n, (cost j + 2)) := by
  rintro v rfl
  obtain ⟨k, hk, hr⟩ := while_chain_run M test X cost n hbody htest
  exact ⟨k, _, hk, hr, while_step_exit M test (X n) hexit, rfl⟩

end IntegerMultBounds.Machine
