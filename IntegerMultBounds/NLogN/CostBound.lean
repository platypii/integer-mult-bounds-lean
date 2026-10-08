import IntegerMultBounds.NLogN.RecurrenceParams

/-! Closing the loop between the operation-count model and the recurrence.
The paper's grid for dimension `d` has the exponents `modelExponents d n`
on its first `d − 1` factors and the root size as its last factor, so the
model's bound `main_ops_le` applies. Any cost `M : ℕ → ℕ` that, above
`2^(1729^12)`, is at most three convolution pipelines at the paper's
parameters plus a linear overhead satisfies the real recursive inequality
with constant `(2880 + C) / log 2`, hence is `O(n log n)` by
`n_log_n_of_rec`. A polynomial base case suffices. The link from `M` to an
actual algorithm's operation count, bit costs, and tape steps is not here. -/

namespace IntegerMultBounds.NLogN

/-- The exponents of the first `d − 1` factors of the paper's grid: `d₀`
factors `r/2` and the rest `r`; the last factor is `r` itself. -/
def modelExponents (d n : ℕ) (i : Fin (d - 1)) : ℕ :=
  if i.val < dimShift d n then rootExp d n - 1 else rootExp d n

theorem two_pow_modelExponents (d n : ℕ) (i : Fin (d - 1)) :
    2 ^ modelExponents d n i = factorAt d n i.val := by
  unfold modelExponents factorAt
  split_ifs <;> rfl

/-- The last factor of the grid is the root size, and the first `d − 1`
factors multiply to `T / r`. -/
theorem modelExponents_prod {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    rootSize d n * ∏ i : Fin (d - 1), 2 ^ modelExponents d n i = transformSize n := by
  have hk : 1 ≤ rootExp d n := by have := rootExp_ge_two hd hn; omega
  have hprod := factorAt_prod (n := n) (by omega : 1 ≤ d) hk
  have hsplit : d = (d - 1) + 1 := by omega
  rw [hsplit, Finset.prod_range_succ] at hprod
  have hlast : factorAt d n (d - 1) = rootSize d n := by
    unfold factorAt rootSize
    have := dimShift_lt (n := n) (by omega : 1 ≤ d)
    have hc : ¬ (d - 1 < dimShift d n) := by omega
    simp only [hc, ↓reduceIte]
  rw [← hsplit] at hprod
  rw [hlast] at hprod
  rw [← hprod, mul_comm]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun i => factorAt d n i) (d - 1)]
  exact Finset.prod_congr rfl fun i _ => two_pow_modelExponents d n i

/-- `log₂ n · log 2 ≤ log n`. -/
theorem natLog_mul_log_two_le {n : ℕ} (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
  have h : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h' : ((2 : ℝ) ^ Nat.log 2 n) ≤ n := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rwa [Real.log_pow] at this

/-- The model's bound at the paper's parameters, as the real recursive
inequality with constant `(2880 + C) / log 2`. -/
theorem cost_rec_real {n : ℕ} (hn : 2 ^ (1729 ^ 12) ≤ n) (M : ℕ → ℕ) (C : ℕ)
    (hM : M n ≤ 3 * pipelineOps (rootSize 1729 n) (precision n) (modelExponents 1729 n) M
      + C * n) :
    (M n : ℝ) ≤ 12 * (transformSize n : ℝ) / rootSize 1729 n *
      (M (3 * rootSize 1729 n * precision n) : ℝ) +
      ((2880 + C) / Real.log 2) * n * Real.log n := by
  have hd : 2 ≤ 1729 := by norm_num
  have hT := modelExponents_prod hd hn
  have hops := main_ops_le hd hn (modelExponents 1729 n) hT M
  have hM' := le_trans hM (Nat.add_le_add_right hops _)
  have hn2 : 2 ≤ n := le_trans (two_le_two_pow_pow (d := 1729) (by norm_num)) hn
  clear hn hM hops
  -- make the grid product an atom so no tactic unfolds it
  set P : ℕ := ∏ i : Fin (1729 - 1), 2 ^ modelExponents 1729 n i with hP
  clear_value P
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
  have hr : (0 : ℝ) < rootSize 1729 n := by exact_mod_cast rootSize_pos 1729 n
  have hTP : 12 * (transformSize n : ℝ) / rootSize 1729 n = 12 * (P : ℝ) := by
    rw [div_eq_iff hr.ne', ← hT]
    push_cast
    ring
  rw [hTP]
  have hnat : (M n : ℝ) ≤ 12 * (P : ℝ) * (M (3 * rootSize 1729 n * precision n) : ℝ) +
      2880 * n * (Nat.log 2 n : ℝ) + C * n := by
    exact_mod_cast hM'
  clear hM' hT
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := natLog_mul_log_two_le hn1
  have hln : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hL : (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ hl2]; exact hlog
  have h1 : (1 : ℝ) ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ hl2, one_mul]; exact hln
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hsplit : ((2880 + C) / Real.log 2) * n * Real.log n =
      2880 * n * (Real.log n / Real.log 2) + C * n * (Real.log n / Real.log 2) := by
    field_simp
  rw [hsplit]
  have h2 : 2880 * (n : ℝ) * (Nat.log 2 n : ℝ) ≤ 2880 * n * (Real.log n / Real.log 2) :=
    mul_le_mul_of_nonneg_left hL (mul_nonneg (by norm_num) hnn)
  have h3 : (C : ℝ) * n ≤ C * n * (Real.log n / Real.log 2) := by
    calc (C : ℝ) * n = C * n * 1 := by ring
      _ ≤ C * n * (Real.log n / Real.log 2) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hC hnn)
  linarith

/-- A polynomial base case gives the `B n log n` base-case bound needed by
the recurrence, with `n₀` kept symbolic. -/
theorem base_of_bounded (M : ℕ → ℕ) (K n₀ : ℕ)
    (hB : ∀ n, n < n₀ → M n ≤ K * n ^ 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, 2 ≤ n → n < n₀ → (M n : ℝ) ≤ B * n * Real.log n := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K * n₀ / Real.log 2, by positivity, fun n hn2 hn₀ => ?_⟩
  have h := hB n hn₀
  have h' : (M n : ℝ) ≤ K * n ^ 2 := by exact_mod_cast h
  have hn₀' : (n : ℝ) ≤ n₀ := by exact_mod_cast hn₀.le
  have hln : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have h1 : (1 : ℝ) ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ hl2, one_mul]; exact hln
  have hnn : (0 : ℝ) ≤ n := by positivity
  have hK : (0 : ℝ) ≤ K := by positivity
  have hsplit : (K : ℝ) * n₀ / Real.log 2 * n * Real.log n =
      K * n * n₀ * (Real.log n / Real.log 2) := by
    field_simp
  rw [hsplit]
  calc (M n : ℝ) ≤ K * n ^ 2 := h'
    _ = K * n * n := by ring
    _ ≤ K * n * n₀ := by gcongr
    _ = K * n * n₀ * 1 := by ring
    _ ≤ K * n * n₀ * (Real.log n / Real.log 2) := by gcongr

/-- Any cost bounded above `2^(1729^12)` by three convolution pipelines at the
paper's parameters plus a linear overhead, and by `B n log n` below, is
`O(n log n)`. -/
theorem cost_nlogn (M : ℕ → ℕ) (C : ℕ)
    (hM : ∀ n, 2 ^ (1729 ^ 12) ≤ n →
      M n ≤ 3 * pipelineOps (rootSize 1729 n) (precision n) (modelExponents 1729 n) M + C * n)
    (hbase : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, 2 ≤ n → n < 2 ^ (1729 ^ 12) →
      (M n : ℝ) ≤ B * n * Real.log n) :
    ∃ D : ℝ, ∀ n, 2 ≤ n → (M n : ℝ) ≤ D * n * Real.log n :=
  n_log_n_of_rec (M := fun n => (M n : ℝ)) (A := (2880 + C) / Real.log 2)
    (by have := Real.log_pos (show (1:ℝ) < 2 by norm_num); positivity)
    (fun n => by positivity)
    (fun n hn => cost_rec_real hn M C (hM n hn))
    hbase

/-- The same with a polynomial base case. -/
theorem cost_nlogn_of_poly_base (M : ℕ → ℕ) (C K : ℕ)
    (hM : ∀ n, 2 ^ (1729 ^ 12) ≤ n →
      M n ≤ 3 * pipelineOps (rootSize 1729 n) (precision n) (modelExponents 1729 n) M + C * n)
    (hB : ∀ n, n < 2 ^ (1729 ^ 12) → M n ≤ K * n ^ 2) :
    ∃ D : ℝ, ∀ n, 2 ≤ n → (M n : ℝ) ≤ D * n * Real.log n :=
  cost_nlogn M C hM (base_of_bounded M K _ hB)

end IntegerMultBounds.NLogN
