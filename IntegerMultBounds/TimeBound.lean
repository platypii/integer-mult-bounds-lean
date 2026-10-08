import IntegerMultBounds.Asymptotics
import IntegerMultBounds.Machine
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The complete time bound (§8). With precision `p = 6 lg n` and padded volume
`V = Θ(n)`, every operation of the multiplication algorithm costs a fixed
multiple of `V (log p)^k p^(1 - g)` for one of the seven margins `g`, or is a
setup cost polynomial in `p`, or is a fixed multiple of `V` times a quantity
eventually bounded. Since every margin exceeds `κ`, the total is eventually
`O(n (lg n)^(1 - κ))`, the target time of `Machine.ComputesWithin`. These are
statements about cost functions; the costs themselves are supplied by the
algorithm's components. -/

namespace IntegerMultBounds.TimeBound

open Filter Asymptotics Parameters Machine

/-- The working precision, as a real number. -/
noncomputable def precision (n : ℕ) : ℝ := 6 * (lg n : ℝ)

theorem one_le_lg (n : ℕ) : 1 ≤ lg n := le_max_right _ _

theorem six_le_precision (n : ℕ) : 6 ≤ precision n := by
  unfold precision
  have : (1 : ℝ) ≤ lg n := by exact_mod_cast one_le_lg n
  linarith

theorem precision_pos (n : ℕ) : 0 < precision n := by linarith [six_le_precision n]

/-- `lg n` is at least `log n / log 2`. -/
theorem log_le_lg (n : ℕ) : Real.log n / Real.log 2 ≤ lg n := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ h2]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, Real.log_zero]
    positivity
  have hle : n ≤ 2 ^ lg n := by
    calc n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
      _ ≤ 2 ^ lg n := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have hle' : (n : ℝ) ≤ (2 : ℝ) ^ (lg n : ℕ) := by exact_mod_cast hle
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  calc Real.log n ≤ Real.log ((2 : ℝ) ^ (lg n : ℕ)) :=
        (Real.log_le_log_iff hnpos (by positivity)).mpr hle'
    _ = (lg n : ℝ) * Real.log 2 := by rw [Real.log_pow]

/-- `lg n` is at most `2 log n / log 2` for `n ≥ 4`. -/
theorem lg_le_log (n : ℕ) (hn : 4 ≤ n) : (lg n : ℝ) ≤ 2 * (Real.log n / Real.log 2) := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hclog : Nat.clog 2 n ≤ Nat.log 2 n + 1 := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    exact (Nat.lt_pow_succ_log_self (by norm_num) n).le
  have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have h' : ((2 : ℝ) ^ (Nat.log 2 n : ℕ)) ≤ n := by exact_mod_cast h
    have := (Real.log_le_log_iff (by positivity) (by positivity : (0 : ℝ) < n)).mpr h'
    rwa [Real.log_pow] at this
  have hlog1 : 1 ≤ Nat.log 2 n := by
    rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
    omega
  have hlg : lg n ≤ Nat.log 2 n + 1 := by
    unfold lg
    exact max_le hclog (by omega)
  have hlg' : (lg n : ℝ) ≤ Nat.log 2 n + 1 := by exact_mod_cast hlg
  have hlog1' : (1 : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hlog1
  calc (lg n : ℝ) ≤ Nat.log 2 n + 1 := hlg'
    _ ≤ 2 * (Nat.log 2 n : ℝ) := by linarith
    _ ≤ 2 * (Real.log n / Real.log 2) := by
        gcongr
        rw [le_div_iff₀ h2]
        exact hlog

theorem tendsto_precision : Tendsto precision atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => Real.log n / Real.log 2) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
      (Real.log_pos (by norm_num))
  have h2 : Tendsto (fun n : ℕ => (lg n : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n => log_le_lg n) h1
  exact h2.const_mul_atTop (by norm_num)

/-- The target time dominates `n`, since `lg n ≥ 1`. -/
theorem le_targetTime {κ : ℝ} (hκ1 : κ ≤ 1) (n : ℕ) : (n : ℝ) ≤ targetTime κ n := by
  unfold targetTime
  have : (1 : ℝ) ≤ (lg n : ℝ) ^ (1 - κ) :=
    Real.one_le_rpow (by exact_mod_cast one_le_lg n) (by linarith)
  calc (n : ℝ) = n * 1 := by ring
    _ ≤ n * (lg n : ℝ) ^ (1 - κ) := by gcongr

theorem targetTime_nonneg (κ : ℝ) (n : ℕ) : 0 ≤ targetTime κ n := by
  unfold targetTime
  positivity

section Rows

/-- A dominant row: normalized cost `C (log p)^k p^e`. -/
structure Row where
  C : ℝ
  k : ℝ
  e : ℝ

/-- The cost of a dominant row on volume `V` at precision `p`. -/
noncomputable def Row.cost (r : Row) (V p : ℝ) : ℝ := r.C * V * Real.log p ^ r.k * p ^ r.e

variable {κ : ℝ} (hκ1 : κ ≤ 1) (V : ℕ → ℝ) (cV : ℝ) (hV0 : ∀ n, 0 ≤ V n)
  (hV : ∀ n, V n ≤ cV * n)

include hV0 hV in
theorem cV_nonneg : 0 ≤ cV := by
  have h1 := hV 1
  have h2 := hV0 1
  simp only [Nat.cast_one, mul_one] at h1
  linarith

include hV0 hV in
/-- A dominant row with exponent below `1 - κ` is eventually a fixed multiple of
the target time. -/
theorem row_eventually (r : Row) (hC : 0 ≤ r.C) (he : r.e < 1 - κ) :
    ∀ᶠ n : ℕ in atTop, r.cost (V n) (precision n) ≤
      r.C * cV * 6 ^ (1 - κ) * targetTime κ n := by
  have hsmall := (log_power_absorbed he r.k).def one_pos
  have hcV := cV_nonneg V cV hV0 hV
  filter_upwards [tendsto_precision.eventually hsmall] with n hn
  simp only [Real.norm_eq_abs, one_mul] at hn
  have hp := precision_pos n
  have hlogp : 0 ≤ Real.log (precision n) := Real.log_nonneg (by linarith [six_le_precision n])
  have habs : Real.log (precision n) ^ r.k * precision n ^ r.e ≤ precision n ^ (1 - κ) := by
    rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hn
  have hpow : precision n ^ (1 - κ) = 6 ^ (1 - κ) * (lg n : ℝ) ^ (1 - κ) := by
    unfold precision
    rw [Real.mul_rpow (by norm_num) (by positivity)]
  unfold Row.cost targetTime
  calc r.C * V n * Real.log (precision n) ^ r.k * precision n ^ r.e
      = r.C * V n * (Real.log (precision n) ^ r.k * precision n ^ r.e) := by ring
    _ ≤ r.C * (cV * n) * precision n ^ (1 - κ) := by
        gcongr
        exact hV n
    _ = r.C * cV * 6 ^ (1 - κ) * (n * (lg n : ℝ) ^ (1 - κ)) := by rw [hpow]; ring

include hκ1 in
/-- A setup cost polynomial in the precision is eventually below the target time. -/
theorem setup_eventually (D A : ℝ) (hD : 0 ≤ D) (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop, D * precision n ^ A ≤ D * targetTime κ n := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < 12 / Real.log 2 := by positivity
  have hcA : 0 < (12 / Real.log 2) ^ A := Real.rpow_pos_of_pos hc A
  -- `(6 lg n)^A ≤ (12 log n / log 2)^A`, and `(log n)^A = o(n)` with constant `1 / c^A`.
  have hsmall := (log_power_absorbed (show (0 : ℝ) < 1 by norm_num) A).def
    (one_div_pos.mpr hcA)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hsmall, eventually_ge_atTop 4]
    with n hn hn4
  simp only [Real.norm_eq_abs, Real.rpow_zero, mul_one, Real.rpow_one] at hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hn
  have hbound : precision n ≤ 12 / Real.log 2 * Real.log n := by
    unfold precision
    have := lg_le_log n hn4
    calc 6 * (lg n : ℝ) ≤ 6 * (2 * (Real.log n / Real.log 2)) := by gcongr
      _ = 12 / Real.log 2 * Real.log n := by ring
  have hp : precision n ^ A ≤ (12 / Real.log 2) ^ A * Real.log n ^ A := by
    rw [← Real.mul_rpow hc.le hlogn]
    exact Real.rpow_le_rpow (precision_pos n).le hbound hA
  have hn' : (12 / Real.log 2) ^ A * Real.log n ^ A ≤ n := by
    have := mul_le_mul_of_nonneg_left hn hcA.le
    rwa [← mul_assoc, mul_one_div_cancel hcA.ne', one_mul] at this
  calc D * precision n ^ A ≤ D * n := by
        apply mul_le_mul_of_nonneg_left _ hD
        exact hp.trans hn'
    _ ≤ D * targetTime κ n := by
        apply mul_le_mul_of_nonneg_left _ hD
        exact le_targetTime hκ1 n

include hκ1 hV0 hV in
/-- A fixed multiple of the volume times an eventually bounded quantity. -/
theorem bounded_eventually (D B : ℝ) (hD : 0 ≤ D) (hB : 0 ≤ B) (φ : ℝ → ℝ)
    (hφ : ∀ᶠ p in atTop, φ p ≤ B) :
    ∀ᶠ n : ℕ in atTop, D * V n * φ (precision n) ≤ D * B * cV * targetTime κ n := by
  have hcV := cV_nonneg V cV hV0 hV
  filter_upwards [tendsto_precision.eventually hφ] with n hn
  calc D * V n * φ (precision n) ≤ D * V n * B :=
        mul_le_mul_of_nonneg_left hn (mul_nonneg hD (hV0 n))
    _ ≤ D * (cV * n) * B := by
        apply mul_le_mul_of_nonneg_right _ hB
        exact mul_le_mul_of_nonneg_left (hV n) hD
    _ ≤ D * B * cV * targetTime κ n := by
        have := le_targetTime hκ1 n
        have h : 0 ≤ D * B * cV := by positivity
        calc D * (cV * n) * B = D * B * cV * n := by ring
          _ ≤ D * B * cV * targetTime κ n := by gcongr

/-- Finitely many eventual bounds by multiples of the target time add up. -/
theorem list_eventually {α : Type*} (κ : ℝ) (l : List α) (f : α → ℕ → ℝ) (g : α → ℝ)
    (h : ∀ a ∈ l, ∀ᶠ n : ℕ in atTop, f a n ≤ g a * targetTime κ n) :
    ∀ᶠ n : ℕ in atTop, (l.map fun a => f a n).sum ≤ (l.map g).sum * targetTime κ n := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    have ha := h a (List.mem_cons_self)
    have hrest := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    filter_upwards [ha, hrest] with n hna hnr
    simp only [List.map_cons, List.sum_cons]
    linarith

end Rows

/-- The complete time bound: dominant rows with exponents below `1 - κ`, setup
costs polynomial in the precision, and volume times eventually bounded
quantities sum to a fixed multiple of the target time for all large `n`. -/
theorem complete_time_bound {κ : ℝ} (hκ1 : κ ≤ 1) (V : ℕ → ℝ) (cV : ℝ) (hV0 : ∀ n, 0 ≤ V n)
    (hV : ∀ n, V n ≤ cV * n)
    (rows : List Row) (hrows : ∀ r ∈ rows, 0 ≤ r.C ∧ 0 ≤ r.k ∧ r.e < 1 - κ)
    (setup : List (ℝ × ℝ)) (hsetup : ∀ s ∈ setup, 0 ≤ s.1 ∧ 0 ≤ s.2)
    (bounded : List (ℝ × (ℝ → ℝ) × ℝ))
    (hbounded : ∀ b ∈ bounded, 0 ≤ b.1 ∧ 0 ≤ b.2.2 ∧ ∀ᶠ p in atTop, b.2.1 p ≤ b.2.2)
    (total : ℕ → ℝ)
    (htotal : ∀ n, total n ≤ (rows.map fun r => r.cost (V n) (precision n)).sum +
      (setup.map fun s => s.1 * precision n ^ s.2).sum +
      (bounded.map fun b => b.1 * V n * b.2.1 (precision n)).sum) :
    ∃ (C : ℝ) (n₀ : ℕ), 0 < C ∧ ∀ n, n₀ ≤ n → total n ≤ C * targetTime κ n := by
  have h1 := list_eventually κ rows (fun r n => r.cost (V n) (precision n))
    (fun r => r.C * cV * 6 ^ (1 - κ)) fun r hr =>
      row_eventually V cV hV0 hV r (hrows r hr).1 (hrows r hr).2.2
  have h2 := list_eventually κ setup (fun s n => s.1 * precision n ^ s.2) (fun s => s.1)
    fun s hs => setup_eventually hκ1 s.1 s.2 (hsetup s hs).1 (hsetup s hs).2
  have h3 := list_eventually κ bounded (fun b n => b.1 * V n * b.2.1 (precision n))
    (fun b => b.1 * b.2.2 * cV) fun b hb =>
      bounded_eventually hκ1 V cV hV0 hV b.1 b.2.2 (hbounded b hb).1 (hbounded b hb).2.1 b.2.1
        (hbounded b hb).2.2
  set K := (rows.map fun r => r.C * cV * 6 ^ (1 - κ)).sum + (setup.map fun s => s.1).sum +
    (bounded.map fun b => b.1 * b.2.2 * cV).sum with hK
  have hall : ∀ᶠ n : ℕ in atTop, total n ≤ (K + 1) * targetTime κ n := by
    filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
    have ht := targetTime_nonneg κ n
    calc total n ≤ _ := htotal n
      _ ≤ K * targetTime κ n := by rw [hK]; linarith
      _ ≤ (K + 1) * targetTime κ n := by nlinarith
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hall
  refine ⟨K + 1, n₀, ?_, hn₀⟩
  -- `K` is a sum of nonnegative terms.
  have hcV := cV_nonneg V cV hV0 hV
  have hK0 : 0 ≤ K := by
    rw [hK]
    have ha : 0 ≤ (rows.map fun r => r.C * cV * 6 ^ (1 - κ)).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
        have := (hrows r hr).1
        positivity
    have hb : 0 ≤ (setup.map fun s => s.1).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
        exact (hsetup s hs).1
    have hc : 0 ≤ (bounded.map fun b => b.1 * b.2.2 * cV).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
        have := (hbounded b hb).1
        have := (hbounded b hb).2.1
        positivity
    linarith
  linarith

/-- The seven assembly rows of the manuscript's cost table, with the exponents
`1 - margin i` and arbitrary nonnegative constants and logarithmic powers. -/
noncomputable def assemblyRows (C k : Fin 7 → ℝ) : List Row :=
  List.ofFn fun i => ⟨C i, k i, 1 - margin i⟩

theorem assemblyRows_admissible (C k : Fin 7 → ℝ) (hC : ∀ i, 0 ≤ C i) (hk : ∀ i, 0 ≤ k i) :
    ∀ r ∈ assemblyRows C k, 0 ≤ r.C ∧ 0 ≤ r.k ∧ r.e < 1 - kappa := by
  intro r hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  refine ⟨hC i, hk i, ?_⟩
  have := margin_strict i
  show 1 - margin i < 1 - kappa
  linarith

theorem kappa_le_one : kappa ≤ 1 := by norm_num [kappa]

/-- The multiplication time bound with the witness parameters: the seven table
rows, polynomial setup, and bounded overheads give `O(n (lg n)^(1 - κ))` with
`κ = 83 / 10^12`, the exponent of `Machine.EndToEnd`. -/
theorem multiplication_time_bound (V : ℕ → ℝ) (cV : ℝ) (hV0 : ∀ n, 0 ≤ V n)
    (hV : ∀ n, V n ≤ cV * n) (C k : Fin 7 → ℝ) (hC : ∀ i, 0 ≤ C i) (hk : ∀ i, 0 ≤ k i)
    (setup : List (ℝ × ℝ)) (hsetup : ∀ s ∈ setup, 0 ≤ s.1 ∧ 0 ≤ s.2)
    (bounded : List (ℝ × (ℝ → ℝ) × ℝ))
    (hbounded : ∀ b ∈ bounded, 0 ≤ b.1 ∧ 0 ≤ b.2.2 ∧ ∀ᶠ p in atTop, b.2.1 p ≤ b.2.2)
    (total : ℕ → ℝ)
    (htotal : ∀ n, total n ≤
      ((assemblyRows C k).map fun r => r.cost (V n) (precision n)).sum +
      (setup.map fun s => s.1 * precision n ^ s.2).sum +
      (bounded.map fun b => b.1 * V n * b.2.1 (precision n)).sum) :
    ∃ (C : ℝ) (n₀ : ℕ), 0 < C ∧ ∀ n, n₀ ≤ n → total n ≤ C * targetTime (83 / 10 ^ 12) n :=
  complete_time_bound kappa_le_one V cV hV0 hV (assemblyRows C k)
    (assemblyRows_admissible C k hC hk) setup hsetup bounded hbounded total htotal

end IntegerMultBounds.TimeBound
