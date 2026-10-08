import IntegerMultBounds.NLogN.Neumann
import IntegerMultBounds.NLogN.Approx
import Mathlib.Algebra.Ring.GeomSum

/-! Lemma 4.12 of Harvey–van der Hoeven: approximating the inverse `J = (1 + E)⁻¹`
with `‖E‖ ≤ 1/2`. Proved: the truncated Neumann series `∑_{i<K} (-E)^i` is within
`2 (1/2)^K` of `J` in operator norm; the Horner recursion `y₀ = v`,
`y_{i+1} = rd (v - E' y_i)` with an approximate `E'` and a rounding `rd` stays in
the ball of radius two and, because the exact `E` damps by one half, has scaled
error at most `2 (εE + ρ)` uniformly in the number of steps; after `p` steps the
total scaled error against `J v` is at most `2 (εE + ρ) + 1`. Bit costs and the
particular `E` of the resampling system are not here. -/

namespace IntegerMultBounds.NLogN

open ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The truncated Neumann series `∑_{i<K} (-E)^i`. -/
noncomputable def neumannPartial (E : V →L[ℂ] V) (K : ℕ) : V →L[ℂ] V :=
  ∑ i ∈ Finset.range K, (-E) ^ i

theorem neumannPartial_mul (E : V →L[ℂ] V) (K : ℕ) :
    neumannPartial E K * (1 + E) = 1 - (-E) ^ K := by
  have := geom_sum_mul_neg (-E) K
  rwa [sub_neg_eq_add] at this

theorem norm_one_clm_le : ‖(1 : V →L[ℂ] V)‖ ≤ 1 := by
  rw [one_def]; exact norm_id_le

/-- `‖J‖ ≤ 2` for any right inverse `J` of `1 + E` with `‖E‖ ≤ 1/2`. -/
theorem norm_inv_le_two {E J : V →L[ℂ] V} (hE : ‖E‖ ≤ 1 / 2) (hJ : (1 + E) ∘L J = 1) :
    ‖J‖ ≤ 2 := by
  have h : J = 1 - E ∘L J := by
    have : (1 + E) ∘L J = J + E ∘L J := by rw [add_comp, one_def, id_comp]
    rw [this] at hJ
    rw [← hJ]; abel
  have h1 : ‖J‖ ≤ 1 + ‖E‖ * ‖J‖ := by
    calc ‖J‖ = ‖1 - E ∘L J‖ := by rw [← h]
      _ ≤ ‖(1 : V →L[ℂ] V)‖ + ‖E ∘L J‖ := norm_sub_le _ _
      _ ≤ 1 + ‖E‖ * ‖J‖ := add_le_add norm_one_clm_le (opNorm_comp_le _ _)
  nlinarith [norm_nonneg J]

theorem norm_neg_pow_le (E : V →L[ℂ] V) (hE : ‖E‖ ≤ 1 / 2) (K : ℕ) :
    ‖(-E) ^ K‖ ≤ (1 / 2) ^ K := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simpa using norm_one_clm_le
  · calc ‖(-E) ^ K‖ ≤ ‖-E‖ ^ K := norm_pow_le' _ hK
      _ ≤ (1 / 2) ^ K := by
        rw [norm_neg]; exact pow_le_pow_left₀ (norm_nonneg _) hE K

/-- The truncated series is within `2 (1/2)^K` of the inverse. -/
theorem norm_neumannPartial_sub_inv {E J : V →L[ℂ] V} (hE : ‖E‖ ≤ 1 / 2)
    (hJ : (1 + E) ∘L J = 1) (K : ℕ) :
    ‖neumannPartial E K - J‖ ≤ 2 * (1 / 2) ^ K := by
  have hJ2 := norm_inv_le_two hE hJ
  have key : neumannPartial E K - J = -((-E) ^ K * J) := by
    have h1 : neumannPartial E K * (1 + E) * J = neumannPartial E K := by
      rw [mul_assoc, mul_def (1 + E) J, hJ, mul_one]
    calc neumannPartial E K - J = (neumannPartial E K * (1 + E) - 1) * J := by
          rw [sub_mul, one_mul, h1]
      _ = -((-E) ^ K * J) := by rw [neumannPartial_mul]; noncomm_ring
  rw [key, norm_neg]
  calc ‖(-E) ^ K * J‖ ≤ ‖(-E) ^ K‖ * ‖J‖ := norm_mul_le _ _
    _ ≤ (1 / 2) ^ K * 2 := by
      apply mul_le_mul (norm_neg_pow_le E hE K) hJ2 (norm_nonneg _) (by positivity)
    _ = 2 * (1 / 2) ^ K := by ring

theorem norm_neumannPartial_sub_inv_pow {E J : V →L[ℂ] V} (hE : ‖E‖ ≤ 1 / 2)
    (hJ : (1 + E) ∘L J = 1) (p : ℕ) :
    ‖neumannPartial E (p + 1) - J‖ ≤ 1 / 2 ^ p := by
  calc ‖neumannPartial E (p + 1) - J‖ ≤ 2 * (1 / 2) ^ (p + 1) :=
        norm_neumannPartial_sub_inv hE hJ _
    _ = 1 / 2 ^ p := by rw [pow_succ, one_div_pow]; ring

/-- Horner evaluation of the Neumann series with an approximate `E'` and a rounding
`rd` after every step: `y₀ = v`, `y_{i+1} = rd (v - E' y_i)`. -/
def hornerNeumannR (rd : V → V) (E' : V → V) (v : V) : ℕ → V
  | 0 => v
  | K + 1 => rd (v - E' (hornerNeumannR rd E' v K))

/-- Horner evaluation without rounding. -/
abbrev hornerNeumann (E' : V → V) (v : V) : ℕ → V := hornerNeumannR id E' v

/-- With the exact map the recursion computes the truncated series `∑_{i≤K} (-E)^i v`. -/
theorem hornerNeumann_exact (E : V →L[ℂ] V) (v : V) (K : ℕ) :
    hornerNeumann E v K = ∑ i ∈ Finset.range (K + 1), ((-E) ^ i) v := by
  induction K with
  | zero => simp [hornerNeumann, hornerNeumannR]
  | succ K ih =>
    rw [Finset.sum_range_succ' (fun i => ((-E) ^ i) v)]
    simp only [hornerNeumann, hornerNeumannR, id, ih, pow_zero]
    rw [map_sum, sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ', mul_apply_eq_comp, neg_apply]

theorem hornerNeumann_eq_partial (E : V →L[ℂ] V) (v : V) (K : ℕ) :
    hornerNeumann E v K = neumannPartial E (K + 1) v := by
  rw [hornerNeumann_exact, neumannPartial]
  simp [sum_apply]

section Error

variable {E : V →L[ℂ] V} {E' rd : V → V} {v : V} {p : ℕ} {εE ρ : ℝ}

/-- Ball invariant and uniform error of the rounded Horner recursion against the exact
one, by geometric damping: `δ_{i+1} ≤ εE + ρ + (1/2) δ_i` keeps `δ ≤ 2 (εE + ρ)`. -/
theorem hornerNeumannR_err (hE : ‖E‖ ≤ 1 / 2)
    (hE' : ∀ y, ‖y‖ ≤ 2 → 2 ^ p * ‖E' y - E y‖ ≤ εE)
    (hE'ball : ∀ y, ‖y‖ ≤ 2 → ‖E' y‖ ≤ 1)
    (hrd : ∀ x, 2 ^ p * ‖rd x - x‖ ≤ ρ) (hrdball : ∀ x, ‖rd x‖ ≤ ‖x‖)
    (hv : ‖v‖ ≤ 1) (K : ℕ) :
    ‖hornerNeumannR rd E' v K‖ ≤ 2 ∧
      2 ^ p * ‖hornerNeumannR rd E' v K - hornerNeumann E v K‖ ≤ 2 * (εE + ρ) := by
  have hεE : 0 ≤ εE := by
    have := hE' v (by linarith)
    have h2 : (0 : ℝ) ≤ 2 ^ p * ‖E' v - E v‖ := by positivity
    linarith
  have hρ : 0 ≤ ρ := by
    have := hrd v
    have h2 : (0 : ℝ) ≤ 2 ^ p * ‖rd v - v‖ := by positivity
    linarith
  induction K with
  | zero =>
    refine ⟨by simpa [hornerNeumannR] using hv.trans (by norm_num), ?_⟩
    simp only [hornerNeumannR, hornerNeumann, sub_self, norm_zero, mul_zero]
    linarith
  | succ K ih =>
    obtain ⟨hball, herr⟩ := ih
    set y' := hornerNeumannR rd E' v K
    set y := hornerNeumann E v K
    refine ⟨?_, ?_⟩
    · calc ‖rd (v - E' y')‖ ≤ ‖v - E' y'‖ := hrdball _
        _ ≤ ‖v‖ + ‖E' y'‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add hv (hE'ball _ hball)
        _ = 2 := by norm_num
    · have h1 : 2 ^ p * ‖rd (v - E' y') - (v - E' y')‖ ≤ ρ := hrd _
      have h2 : 2 ^ p * ‖E' y' - E y'‖ ≤ εE := hE' _ hball
      have h3 : ‖E y' - E y‖ ≤ 1 / 2 * ‖y' - y‖ := by
        rw [← map_sub]
        calc ‖E (y' - y)‖ ≤ ‖E‖ * ‖y' - y‖ := le_opNorm _ _
          _ ≤ 1 / 2 * ‖y' - y‖ := by gcongr
      have hp : (0 : ℝ) < 2 ^ p := by positivity
      have htri : ‖rd (v - E' y') - (v - E y)‖ ≤
          ‖rd (v - E' y') - (v - E' y')‖ + ‖E' y' - E y'‖ + ‖E y' - E y‖ := by
        have : rd (v - E' y') - (v - E y) =
            (rd (v - E' y') - (v - E' y')) + (E y' - E' y') + (E y - E y') := by abel
        rw [this]
        calc ‖rd (v - E' y') - (v - E' y') + (E y' - E' y') + (E y - E y')‖
            ≤ ‖rd (v - E' y') - (v - E' y') + (E y' - E' y')‖ + ‖E y - E y'‖ :=
              norm_add_le _ _
          _ ≤ ‖rd (v - E' y') - (v - E' y')‖ + ‖E y' - E' y'‖ + ‖E y - E y'‖ :=
              add_le_add (norm_add_le _ _) le_rfl
          _ = _ := by rw [norm_sub_rev (E y') (E' y'), norm_sub_rev (E y) (E y')]
      show 2 ^ p * ‖rd (v - E' y') - id (v - E y)‖ ≤ 2 * (εE + ρ)
      simp only [id]
      calc 2 ^ p * ‖rd (v - E' y') - (v - E y)‖
          ≤ 2 ^ p * (‖rd (v - E' y') - (v - E' y')‖ + ‖E' y' - E y'‖ + ‖E y' - E y‖) := by
            gcongr
        _ = 2 ^ p * ‖rd (v - E' y') - (v - E' y')‖ + 2 ^ p * ‖E' y' - E y'‖ +
              2 ^ p * ‖E y' - E y‖ := by ring
        _ ≤ ρ + εE + 1 / 2 * (2 ^ p * ‖y' - y‖) := by
            have : 2 ^ p * ‖E y' - E y‖ ≤ 1 / 2 * (2 ^ p * ‖y' - y‖) := by
              calc 2 ^ p * ‖E y' - E y‖ ≤ 2 ^ p * (1 / 2 * ‖y' - y‖) := by gcongr
                _ = 1 / 2 * (2 ^ p * ‖y' - y‖) := by ring
            linarith
        _ ≤ ρ + εE + 1 / 2 * (2 * (εE + ρ)) := by gcongr
        _ = 2 * (εE + ρ) := by ring

/-- The unrounded Horner recursion with an approximate `E'` has scaled error at most
`2 εE`, uniformly in the number of steps. -/
theorem hornerNeumann_err (hE : ‖E‖ ≤ 1 / 2)
    (hE' : ∀ y, ‖y‖ ≤ 2 → 2 ^ p * ‖E' y - E y‖ ≤ εE)
    (hE'ball : ∀ y, ‖y‖ ≤ 2 → ‖E' y‖ ≤ 1) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    2 ^ p * ‖hornerNeumann E' v K - hornerNeumann E v K‖ ≤ 2 * εE := by
  have := (hornerNeumannR_err (rd := id) (ρ := 0) hE hE' hE'ball
    (fun x => by simp) (fun x => le_rfl) hv K).2
  simpa using this

/-- Lemma 4.12: `p` rounded Horner steps approximate `J v = (1 + E)⁻¹ v` with scaled
error at most `2 (εE + ρ) + 1`. -/
theorem inverse_approx {J : V →L[ℂ] V} (hE : ‖E‖ ≤ 1 / 2) (hJ : (1 + E) ∘L J = 1)
    (hE' : ∀ y, ‖y‖ ≤ 2 → 2 ^ p * ‖E' y - E y‖ ≤ εE)
    (hE'ball : ∀ y, ‖y‖ ≤ 2 → ‖E' y‖ ≤ 1)
    (hrd : ∀ x, 2 ^ p * ‖rd x - x‖ ≤ ρ) (hrdball : ∀ x, ‖rd x‖ ≤ ‖x‖)
    (hv : ‖v‖ ≤ 1) :
    2 ^ p * ‖hornerNeumannR rd E' v p - J v‖ ≤ 2 * (εE + ρ) + 1 := by
  have h1 := (hornerNeumannR_err hE hE' hE'ball hrd hrdball hv p).2
  have h2 : ‖hornerNeumann E v p - J v‖ ≤ 1 / 2 ^ p := by
    rw [hornerNeumann_eq_partial, ← sub_apply]
    calc ‖(neumannPartial E (p + 1) - J) v‖
        ≤ ‖neumannPartial E (p + 1) - J‖ * ‖v‖ := le_opNorm _ _
      _ ≤ 1 / 2 ^ p * 1 := by
        gcongr
        exact norm_neumannPartial_sub_inv_pow hE hJ p
      _ = 1 / 2 ^ p := mul_one _
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h3 : 2 ^ p * ‖hornerNeumann E v p - J v‖ ≤ 1 := by
    calc 2 ^ p * ‖hornerNeumann E v p - J v‖ ≤ 2 ^ p * (1 / 2 ^ p) := by gcongr
      _ = 1 := by field_simp
  calc 2 ^ p * ‖hornerNeumannR rd E' v p - J v‖
      ≤ 2 ^ p * (‖hornerNeumannR rd E' v p - hornerNeumann E v p‖ +
          ‖hornerNeumann E v p - J v‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = 2 ^ p * ‖hornerNeumannR rd E' v p - hornerNeumann E v p‖ +
          2 ^ p * ‖hornerNeumann E v p - J v‖ := by ring
    _ ≤ 2 * (εE + ρ) + 1 := add_le_add h1 h3

end Error

end IntegerMultBounds.NLogN
