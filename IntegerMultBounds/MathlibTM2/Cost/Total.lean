module

public import IntegerMultBounds.MathlibTM2.Cost.Growth
import IntegerMultBounds.MathlibTM2.Layer.Recurrence
public import IntegerMultBounds.Parameters
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# Shared analytic bounds and the legacy quadratic CRT envelope

`totBound C n` is `C` times the sum of the stage costs of `docs/fast-pipeline.md` at operand
length `n`, each written in the parameters of `Mult/Sizes.lean`. One `p`-bit product costs
`M(p) = p^{1+δ}` with `δ = 1/128` (`totMp`); `gr_mLogLog_le` bounds the Schönhage–Strassen step
count `m (log m + 1)(log log m + 1)` of `Host/SSMul` by `262144 m^{1+δ}`.

| term | stages | form |
|---|---|---|
| `n` | F1, F3, F11 | input, digits, carries, output |
| `2 totCRT` | F4, F9 | `T p d² (1 + ℓ^τ)` per CRT reindexing |
| `3 totResamp` | `Ã`, `B̃₀` in F5, F6, F8 | `d T p^{1/2} α M(p) = d T p^{3/2+δ} α` |
| `3 totConv` | convolution in F5, F6, F8 | `T p (d K + p K^{τ-1} + ℓ d^{λ'} + grLogLog (r p))` |
| `3 T M(p)` | chirp products and twists in F5, F6, F8 | |
| `T M(p)` | F7 pointwise products | |
| `S M(p)` | F10 final scaling | |
| `T p` | F2 tables | |
| `n + B^C` | F2 parameter machine | |

Exponents: `τ = 1 - 123899714039/10¹⁵`, `σ = 1 - 418/10¹²` (`IntegerMultBounds.Parameters`), `β = 1/2`,
`λ = 1 - 3/10¹⁰` (`totLam`), `λ' = 1 - 1/10¹¹` (`totLam'`), and
`κ = ε c (1 - τ) = 3840891135209 / (10¹⁵ · 2³⁸)` (`totKappa`, `tot_kappa_eq`). The ring-product factor is
`grLogLog X = (log₂ X + 1)(log₂ (log₂ X + 1) + 1)` (`Cost/Growth`); `gr_ringBound_le` bounds the
packed ring product `rpRingBound N` of `Fast/RingProd` on `N ≤ A r p` bits by a constant times
`r p · grLogLog (r p)`.

With `B = b n` and `T p ≤ 48 n` (`gr_Tp_le`), each term is at most a constant times `n B^x`:

| term | exponent `x` |
|---|---|
| `T p d² (1 + ℓ^τ)` | `τ + ε (2 - τ)`, from `d² ℓ^τ = d^{2-τ} (d ℓ)^τ`, `d ℓ ≤ 2B` |
| `d T p^{1/2} α M(p)` | `7/8 + 3ε/2`, from `α ≤ 4 d^{1/2} B^{1/4}` |
| `T p d K` | `2ε` |
| `T p · p K^{τ-1}` | `1 - ε c (1 - τ) = 1 - κ`, from `B^{εc} ≤ 4K` |
| `T p ℓ d^{λ'}` | `1 - ε (1 - λ')`, from `d ℓ ≤ 2B`, `B^ε ≤ 2d` |
| `T p grLogLog (r p)` | `1 - ε + εc`, from `log₂ (r p) ≤ 8 B^{1-ε}`, `log₂ (log₂ (r p) + 1) ≤ K + 2` |
| `T M(p)`, `S M(p)` | `δ` |
| `n`, `T p`, `n + B^C` | `0` |

For the direct CRT envelope, the largest exponent is `1 - κ`, from
`T p · p K^{τ-1}`. The legacy quadratic CRT exponent exceeds this bound at the
retuned dimension. Its bounds below therefore require an explicit `hCRT`
comparison; the executable pipeline uses the unconditional results in `DirectTotal`.

* `tot_lam_conditions`: `max τ σ < λ < 1`, `τ (1 + c/β) ≤ λ`, `max λ (σ + β(1-σ)) < λ' < 1`;
  `tot_layer_cost_bound` is `Layer.Recurrence.layer_cost_bound` at these exponents.
* `tot_crt_le`, `tot_resamp_le`, `tot_conv_le`, `tot_mp_le`: the term bounds.
* Under `hCRT`, `tot_le`: eventually `totBound C n ≤ 40000 C n B^{1-κ}`.
* Under `hCRT`, `totBound_isBigO_kappa`, `totBound_isBigO`: `totBound C = O(n (log n)^{1-κ})`.
* Under `hCRT`, `tot_htime`: an `ℕ`-valued `time` with `time n ≤ totBound C n` eventually satisfies the
  hypothesis `htime` of `Fast.statement_of_dispatch` at `κ = totKappa`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter Asymptotics IntegerMultBounds

/-! ### Exponents -/

/-- `δ = 1/128`: one `p`-bit product costs `O(p^{1+δ})`. -/
noncomputable def totDelta : ℝ := (2^7:ℝ)⁻¹

/-- `λ = 1 - 3/10¹⁰`, the exponent of the layer recursion. -/
noncomputable def totLam : ℝ := 1 - 3 / 10 ^ 10

/-- `λ' = 1 - 1/10¹¹`, the exponent of the layer cost `O(V d^{λ'})`. -/
noncomputable def totLam' : ℝ := 1 - 1 / 10 ^ 11

/-- `κ = ε c (1 - τ)`. -/
noncomputable def totKappa : ℝ := epsilon * cParam * (1 - Parameters.tau)

theorem tot_kappa_eq : totKappa = 3840891135209 / (10 ^ 15 * 2 ^ 38) := by
  rw [totKappa, epsilon_eq, cParam_eq, Parameters.tau]; norm_num

theorem tot_kappa_pos : 0 < totKappa := by rw [tot_kappa_eq]; norm_num

theorem tot_sigma_nonneg : 0 ≤ Parameters.sigma := by norm_num [Parameters.sigma]

theorem tot_sigma_le_one : Parameters.sigma ≤ 1 := by norm_num [Parameters.sigma]

theorem tot_tau_nonneg : 0 ≤ Parameters.tau := by norm_num [Parameters.tau]

theorem tot_tau_le_one : Parameters.tau ≤ 1 := by norm_num [Parameters.tau]

theorem tot_sigma_lt_lam : Parameters.sigma < totLam := by
  norm_num [Parameters.sigma, totLam]

theorem tot_tau_lt_lam : Parameters.tau < totLam := by norm_num [Parameters.tau, totLam]

theorem tot_lam_lt_one : totLam < 1 := by norm_num [totLam]

/-- `τ (1 + c/β) ≤ λ` at `β = 1/2`. -/
theorem tot_tau_c_le : Parameters.tau * (1 + cParam / (1 / 2)) ≤ totLam := by
  rw [cParam_eq]; norm_num [Parameters.tau, totLam]

theorem tot_lam_lt_lam' : totLam < totLam' := by norm_num [totLam, totLam']

/-- `σ + β (1 - σ) < λ'` at `β = 1/2`. -/
theorem tot_leaf_lt_lam' : Parameters.sigma + 1 / 2 * (1 - Parameters.sigma) < totLam' := by
  norm_num [Parameters.sigma, totLam']

theorem tot_lam'_lt_one : totLam' < 1 := by norm_num [totLam']

/-- The side conditions of `Layer/Recurrence` at `β = 1/2`, `c = cParam`. -/
theorem tot_lam_conditions :
    max Parameters.tau Parameters.sigma < totLam ∧ totLam < 1 ∧
      Parameters.tau * (1 + cParam / (1 / 2)) ≤ totLam ∧
      max totLam (Parameters.sigma + 1 / 2 * (1 - Parameters.sigma)) < totLam' ∧
      totLam' < 1 :=
  ⟨max_lt tot_tau_lt_lam tot_sigma_lt_lam, tot_lam_lt_one, tot_tau_c_le,
    max_lt tot_lam_lt_lam' tot_leaf_lt_lam', tot_lam'_lt_one⟩

/-- `Layer.Recurrence.layer_cost_bound` at `τ = Parameters.tau`, `σ = Parameters.sigma`,
`λ = totLam`, `λ' = totLam'`, `β = 1/2`, `c = cParam`: the normalized layer cost is
`O(d^{λ'})`. -/
theorem tot_layer_cost_bound {m : ℕ} {a C₀ C₁ C₂ Q : ℝ} (hm : 2 ≤ m) (ha : 0 ≤ a)
    (haσ : a ≤ (m : ℝ) ^ Parameters.sigma)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, ∀ d K : ℝ, 1 ≤ d → 0 ≤ K → K ≤ d ^ cParam →
      ∀ j₀ : ℕ, (m : ℝ) ^ j₀ ≤ d ^ (1 / 2 : ℝ) → d ^ (1 / 2 : ℝ) ≤ (m : ℝ) ^ (j₀ + 1) →
      ∀ G : ℕ → ℝ, (∀ j ≤ j₀, G j ≤ C₀ * (m : ℝ) ^ j) →
        (∀ j, j₀ ≤ j → G (j + 1) ≤
          a * G j + C₁ * ((K * (m : ℝ) ^ (j + 1)) ^ Parameters.tau + 1)) →
      ∀ (n : ℕ → ℕ) (k : ℕ), (∀ j, n j < m) →
        ∑ j ∈ Finset.range (k + 1), (n j : ℝ) * (m : ℝ) ^ j ≤ d →
      ∀ q₀ : ℝ, q₀ ≤ Q * (1 + Real.logb m d) →
        ∑ j ∈ Finset.range (k + 1), (n j : ℝ) * G j + q₀ * C₂ ≤ C * d ^ totLam' :=
  IntegerMultBounds.MathlibTM2.Layer.Recurrence.layer_cost_bound hm ha haσ tot_sigma_nonneg tot_sigma_le_one
    tot_sigma_lt_lam tot_tau_nonneg (by norm_num) gr_cParam_pos.le tot_tau_c_le tot_lam_lt_lam'
    tot_leaf_lt_lam' hC₀ hC₁ hC₂ hQ

/-- The direct CRT and shared stage exponent comparisons against `1 - κ`. -/
theorem tot_exp_facts :
    0 ≤ 1 - totKappa ∧ 2 * epsilon ≤ 1 - totKappa ∧
      epsilon * (1 - Parameters.tau) + Parameters.tau ≤ 1 - totKappa ∧
      epsilon + epsilon * cParam * (1 / 2) + (1 / 2 + totDelta) ≤ 1 - totKappa ∧
      1 - epsilon * (1 - totLam') ≤ 1 - totKappa ∧
      1 - epsilon + epsilon * cParam ≤ 1 - totKappa ∧ totDelta ≤ 1 - totKappa := by
  rw [tot_kappa_eq, epsilon_eq, cParam_eq]
  norm_num [Parameters.tau, totLam', totDelta]

/-! ### The stage costs -/

/-- One `p`-bit product, `M(p) = p^{1+δ}`. -/
noncomputable def totMp (n : ℕ) : ℝ := (p n : ℝ) ^ (1 + totDelta)

/-- One CRT reindexing `Φ` or `Φ⁻¹` (F4, F9): `T p d² (1 + ℓ^τ)`. -/
noncomputable def totCRT (n : ℕ) : ℝ :=
  (T n : ℝ) * p n * (d n : ℝ) ^ 2 * (1 + (ℓ n : ℝ) ^ Parameters.tau)

/-- The resamplings `Ã` and `B̃₀` of one transform, `d T p^{1/2} α M(p) = d T p^{3/2+δ} α`:
`d` axis passes over `T` entries with `O(p^{1/2} α)` products of `p` bits per entry. -/
noncomputable def totResamp (n : ℕ) : ℝ :=
  (d n : ℝ) * T n * (p n : ℝ) ^ (1 / 2 : ℝ) * alpha n * totMp n

/-- The synthetic complex convolution of one transform: `T p (d K + p K^{τ-1} + ℓ d^{λ'} +
grLogLog (r p))`. `ℓ d^{λ'}` is the layer cost of the `ℓ` rounds. `grLogLog (r p) =
(log₂ (r p) + 1)(log₂ (log₂ (r p) + 1) + 1)` covers the packed ring products of the
`M = T/r` records: one product on `N ≤ A r p` packed bits costs `O(r p · grLogLog (r p))`
(`gr_ringBound_le`). -/
noncomputable def totConv (n : ℕ) : ℝ :=
  (T n : ℝ) * p n * ((d n : ℝ) * K n + (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) +
    (ℓ n : ℝ) * (d n : ℝ) ^ totLam' + grLogLog ((r n : ℝ) * p n))

/-- The total-time bound: `C` times the stage costs at operand length `n`. -/
noncomputable def totBound (C n : ℕ) : ℝ :=
  C * ((n : ℝ) + 2 * totCRT n + 3 * (totResamp n + totConv n + T n * totMp n) +
    T n * totMp n + S n * totMp n + T n * p n + ((n : ℝ) + (b n : ℝ) ^ C))

/-! ### Term bounds -/

section Terms

variable {n : ℕ}

theorem tot_one_le_b (h : Big n) : (1 : ℝ) ≤ b n := by
  have := h.sixteen_le_b; exact_mod_cast (show 1 ≤ b n by omega)

theorem tot_p_pos (h : Big n) : (0 : ℝ) < p n := by
  have := h.thirteen_le_p; exact_mod_cast (show 0 < p n by omega)

/-- `M(p) = p · p^δ`. -/
theorem tot_mp_eq (h : Big n) : totMp n = (p n : ℝ) * (p n : ℝ) ^ totDelta := by
  rw [totMp, Real.rpow_add (tot_p_pos h), Real.rpow_one]

theorem tot_mp_nonneg (n : ℕ) : 0 ≤ totMp n := by unfold totMp; positivity

/-- `T M(p) ≤ 288 n B^{1-κ}`. -/
theorem tot_mp_le (h : Big n) :
    (T n : ℝ) * totMp n ≤ 288 * ((n : ℝ) * (b n : ℝ) ^ (1 - totKappa)) := by
  obtain ⟨-, -, -, -, -, -, hδ⟩ := tot_exp_facts
  have hB1 := tot_one_le_b h
  have h1 : (p n : ℝ) ^ totDelta ≤ 6 * (b n : ℝ) ^ (1 - totKappa) :=
    gr_le_rpow_of_le hB1 (by norm_num) (gr_p_rpow_le n (by norm_num [totDelta])) hδ
  have h2 := gr_Tp_le h.1
  rw [tot_mp_eq h]
  calc (T n : ℝ) * ((p n : ℝ) * (p n : ℝ) ^ totDelta) = (T n * p n) * (p n : ℝ) ^ totDelta := by
        ring
    _ ≤ (48 * n) * (6 * (b n : ℝ) ^ (1 - totKappa)) :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
    _ = 288 * ((n : ℝ) * (b n : ℝ) ^ (1 - totKappa)) := by ring

/-- The legacy quadratic CRT bound, conditional on its exponent comparison. -/
theorem tot_crt_le
    (hCRT : epsilon * (2 - Parameters.tau) + Parameters.tau ≤ 1 - totKappa) (h : Big n) :
    totCRT n ≤ 144 * ((n : ℝ) * (b n : ℝ) ^ (1 - totKappa)) := by
  obtain ⟨-, h2e, -, -, -, -, -⟩ := tot_exp_facts
  have hcrt := hCRT
  have hB1 := tot_one_le_b h
  have hB : (0 : ℝ) < b n := by linarith
  have hD : (0 : ℝ) < d n := by exact_mod_cast h.one_le_d
  have hτ0 := tot_tau_nonneg
  have hτ1 := tot_tau_le_one
  have hD2 : (d n : ℝ) ^ 2 ≤ (b n : ℝ) ^ (1 - totKappa) := by
    have e : (d n : ℝ) ^ 2 = (d n : ℝ) ^ (2 : ℝ) := by norm_num
    rw [e]
    refine (gr_d_rpow_le n (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith))
  have hDl : (d n : ℝ) ^ 2 * (ℓ n : ℝ) ^ Parameters.tau ≤ 2 * (b n : ℝ) ^ (1 - totKappa) := by
    have e1 : (d n : ℝ) ^ 2 * (ℓ n : ℝ) ^ Parameters.tau =
        (d n : ℝ) ^ (2 - Parameters.tau) * ((d n : ℝ) * ℓ n) ^ Parameters.tau := by
      rw [Real.mul_rpow hD.le (Nat.cast_nonneg _), ← mul_assoc, ← Real.rpow_add hD,
        sub_add_cancel]
      norm_num
    have h1 : (d n : ℝ) ^ (2 - Parameters.tau) ≤
        1 * (b n : ℝ) ^ (epsilon * (2 - Parameters.tau)) := by
      rw [one_mul]; exact gr_d_rpow_le n (by linarith)
    have h2 : ((d n : ℝ) * ℓ n) ^ Parameters.tau ≤ 2 * (b n : ℝ) ^ Parameters.tau :=
      calc ((d n : ℝ) * ℓ n) ^ Parameters.tau ≤ (2 * (b n : ℝ)) ^ Parameters.tau :=
            Real.rpow_le_rpow (by positivity) (gr_dℓ_le h) hτ0
        _ = (2 : ℝ) ^ Parameters.tau * (b n : ℝ) ^ Parameters.tau :=
            Real.mul_rpow (by norm_num) hB.le
        _ ≤ 2 * (b n : ℝ) ^ Parameters.tau := by
            gcongr; exact Real.rpow_le_self_of_one_le (by norm_num) hτ1
    rw [e1]
    have h3 := gr_mul_le hB (by positivity) (by norm_num) h1 h2
    have h4 := gr_le_rpow_of_le hB1 (by norm_num) h3 hcrt
    linarith
  have hsum : (d n : ℝ) ^ 2 * (1 + (ℓ n : ℝ) ^ Parameters.tau) ≤
      3 * (b n : ℝ) ^ (1 - totKappa) := by
    have e : (d n : ℝ) ^ 2 * (1 + (ℓ n : ℝ) ^ Parameters.tau) =
        (d n : ℝ) ^ 2 + (d n : ℝ) ^ 2 * (ℓ n : ℝ) ^ Parameters.tau := by ring
    rw [e]; linarith
  have hTp := gr_Tp_le h.1
  unfold totCRT
  calc (T n : ℝ) * p n * (d n : ℝ) ^ 2 * (1 + (ℓ n : ℝ) ^ Parameters.tau) =
      ((T n : ℝ) * p n) * ((d n : ℝ) ^ 2 * (1 + (ℓ n : ℝ) ^ Parameters.tau)) := by ring
    _ ≤ (48 * n) * (3 * (b n : ℝ) ^ (1 - totKappa)) :=
        mul_le_mul hTp hsum (by positivity) (by positivity)
    _ = 144 * ((n : ℝ) * (b n : ℝ) ^ (1 - totKappa)) := by ring

/-- `d T p^{1/2} α M(p) ≤ 6912 n B^{1-κ}`. -/
theorem tot_resamp_le (h : Big n) (hK : 1 ≤ K n) (hclog : Nat.clog 2 (p n) ≤ K n) :
    totResamp n ≤ 6912 * ((n : ℝ) * (b n : ℝ) ^ (1 - totKappa)) := by
  obtain ⟨-, -, -, hres, -, -, -⟩ := tot_exp_facts
  have hB1 := tot_one_le_b h
  have hB : (0 : ℝ) < b n := by linarith
  have hα : (alpha n : ℝ) ≤ 4 * (b n : ℝ) ^ (epsilon * cParam * (1 / 2)) :=
    gr_alpha_le_K hK hclog
  have hd : (d n : ℝ) ≤ 1 * (b n : ℝ) ^ epsilon := by rw [one_mul]; exact gr_d_le_rpow n
  have hdα := gr_mul_le hB (Nat.cast_nonneg _) (by norm_num) hd hα
  have hp := gr_mul_le hB (by positivity) (by norm_num)
    (gr_p_rpow_le n (x := 1 / 2) (by norm_num))
    (gr_p_rpow_le n (x := totDelta) (by norm_num [totDelta]))
  have h3 := gr_mul_le hB (by positivity) (by norm_num) hdα hp
  have h4 := gr_le_rpow_of_le hB1 (by norm_num) h3 hres
  have hTp := gr_Tp_le h.1
  rw [totResamp, tot_mp_eq h]
  calc (d n : ℝ) * T n * (p n : ℝ) ^ (1 / 2 : ℝ) * alpha n * ((p n : ℝ) * (p n : ℝ) ^ totDelta) =
      ((T n : ℝ) * p n) * (((d n : ℝ) * alpha n) *
        ((p n : ℝ) ^ (1 / 2 : ℝ) * (p n : ℝ) ^ totDelta)) := by ring
    _ ≤ (48 * n) * (1 * 4 * (6 * 6) * (b n : ℝ) ^ (1 - totKappa)) :=
        mul_le_mul hTp h4 (by positivity) (by positivity)
    _ = 6912 * ((n : ℝ) * (b n : ℝ) ^ (1 - totKappa)) := by ring

theorem tot_conv_inner_nonneg (h : Big n) :
    0 ≤ (d n : ℝ) * K n + (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) +
      (ℓ n : ℝ) * (d n : ℝ) ^ totLam' + grLogLog ((r n : ℝ) * p n) := by
  have h1 : 0 ≤ grLogLog ((r n : ℝ) * p n) := by
    have hr : (1 : ℝ) ≤ r n := by rw [gr_r_eq]; exact one_le_pow₀ (by norm_num)
    have hp : (1 : ℝ) ≤ p n := by
      have := h.thirteen_le_p; exact_mod_cast (show 1 ≤ p n by omega)
    have := gr_one_le_logLog (one_le_mul_of_one_le_of_one_le hr hp)
    linarith
  have h2 : (0 : ℝ) ≤ (d n : ℝ) * K n := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h3 : (0 : ℝ) ≤ (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h4 : (0 : ℝ) ≤ (ℓ n : ℝ) * (d n : ℝ) ^ totLam' :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  linarith

/-- `T p (d K + p K^{τ-1} + ℓ d^{λ'} + grLogLog (r p)) ≤ 3120 n B^{1-κ}`, given `K ≥ 1` and
`log₂ p ≤ K`. -/
theorem tot_conv_le (h : Big n) (hK : 1 ≤ K n) (hlogp : Real.logb 2 (p n) ≤ K n) :
    totConv n ≤ 3120 * ((n : ℝ) * (b n : ℝ) ^ (1 - totKappa)) := by
  obtain ⟨-, h2e, -, -, hlam, hll, -⟩ := tot_exp_facts
  have hB1 := tot_one_le_b h
  have hB : (0 : ℝ) < b n := by linarith
  have hD : (0 : ℝ) < d n := by exact_mod_cast h.one_le_d
  have hK0 : (0 : ℝ) < K n := by exact_mod_cast hK
  have hτ0 := tot_tau_nonneg
  have hτ1 := tot_tau_le_one
  -- `d K ≤ d² ≤ B^{2ε}`
  have i1 : (d n : ℝ) * K n ≤ (b n : ℝ) ^ (1 - totKappa) := by
    have hKd : (K n : ℝ) ≤ d n := by exact_mod_cast K_le_d n
    have e : (d n : ℝ) * d n = (d n : ℝ) ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    calc (d n : ℝ) * K n ≤ (d n : ℝ) * d n := mul_le_mul_of_nonneg_left hKd hD.le
      _ = (d n : ℝ) ^ (2 : ℝ) := e
      _ ≤ (b n : ℝ) ^ (epsilon * 2) := gr_d_rpow_le n (by norm_num)
      _ ≤ (b n : ℝ) ^ (1 - totKappa) := Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
  -- `p K^{τ-1} = 6 B / K^{1-τ} ≤ 24 B^{1-κ}`
  have i2 : (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) ≤ 24 * (b n : ℝ) ^ (1 - totKappa) := by
    have hKτ : 0 < (K n : ℝ) ^ (1 - Parameters.tau) := Real.rpow_pos_of_pos hK0 _
    have e : (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) =
        6 * ((b n : ℝ) / (K n : ℝ) ^ (1 - Parameters.tau)) := by
      rw [show Parameters.tau - 1 = -(1 - Parameters.tau) by ring, Real.rpow_neg hK0.le, gr_p_eq]
      ring
    have hk : (b n : ℝ) ^ totKappa ≤ 4 * (K n : ℝ) ^ (1 - Parameters.tau) :=
      gr_rpow_le_four_K_rpow hK (by linarith) (by linarith)
    have := gr_div_le hB hKτ hk
    rw [e]; linarith
  -- `ℓ d^{λ'} = d ℓ / d^{1-λ'} ≤ 2B / d^{1-λ'} ≤ 4 B^{1-ε(1-λ')}`
  have i3 : (ℓ n : ℝ) * (d n : ℝ) ^ totLam' ≤ 4 * (b n : ℝ) ^ (1 - totKappa) := by
    have hl0 : 0 ≤ 1 - totLam' := by have := tot_lam'_lt_one; linarith
    have hl1 : 1 - totLam' ≤ 1 := by
      have : 0 ≤ totLam' := by norm_num [totLam']
      linarith
    have hDl : 0 < (d n : ℝ) ^ (1 - totLam') := Real.rpow_pos_of_pos hD _
    have e : (ℓ n : ℝ) * (d n : ℝ) ^ totLam' =
        ((d n : ℝ) * ℓ n) / (d n : ℝ) ^ (1 - totLam') := by
      have e0 := Real.rpow_sub hD 1 (1 - totLam')
      rw [sub_sub_cancel, Real.rpow_one] at e0
      rw [e0]
      ring
    have h1 : ((d n : ℝ) * ℓ n) / (d n : ℝ) ^ (1 - totLam') ≤
        2 * ((b n : ℝ) / (d n : ℝ) ^ (1 - totLam')) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (gr_dℓ_le h) hDl.le
    have h2 := gr_div_le hB hDl (gr_rpow_le_two_d_rpow h.one_le_d hl0 hl1)
    have h3 := gr_le_rpow_of_le hB1 (by norm_num) h2 hlam
    rw [e]; linarith
  -- `Λ = log₂ (r p) = ℓ + log₂ p ≤ 2ℓ`, so `Λ + 1 ≤ 9 B^{1-ε}` and
  -- `log₂ (Λ + 1) + 1 ≤ log₂ (4p) + 1 ≤ K + 3 ≤ 4 B^{εc}`
  have i4 : grLogLog ((r n : ℝ) * p n) ≤ 36 * (b n : ℝ) ^ (1 - totKappa) := by
    have hp1 : 1 ≤ p n := by have := h.thirteen_le_p; omega
    have hp1' : (1 : ℝ) ≤ p n := by exact_mod_cast hp1
    have hΛ := gr_logb_rp hp1
    have hlp0 : 0 ≤ Real.logb 2 (p n) := gr_logb_nonneg hp1'
    have hKℓ : (K n : ℝ) + 1 ≤ ℓ n := by exact_mod_cast h.K_succ_le_ℓ
    have hℓp : (ℓ n : ℝ) ≤ p n := by
      have h1 : 3 * d n * ℓ n ≤ p n := h.ℓ_bounds.2
      have h2 : ℓ n ≤ 3 * d n * ℓ n := by
        have := h.one_le_d
        nlinarith
      exact_mod_cast h2.trans h1
    unfold grLogLog
    set Λ := Real.logb 2 ((r n : ℝ) * p n) with hΛ_def
    have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
    have hΛℓ : Λ ≤ 2 * ℓ n := by rw [hΛ]; linarith
    have hBe : (1 : ℝ) ≤ (b n : ℝ) ^ (1 - epsilon) :=
      Real.one_le_rpow hB1 (by linarith [gr_epsilon_le_one])
    have f1 : Λ + 1 ≤ 9 * (b n : ℝ) ^ (1 - epsilon) := by
      have := gr_ℓ_le_rpow h
      linarith
    have h4p : Real.logb 2 (4 * p n) = 2 + Real.logb 2 (p n) := by
      rw [Real.logb_mul (by norm_num) (by linarith), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.logb_pow, Real.logb_self_eq_one one_lt_two]
      norm_num
    have hlΛ : Real.logb 2 (Λ + 1) ≤ Real.logb 2 (4 * p n) :=
      Real.logb_le_logb_of_le one_lt_two (by linarith) (by linarith)
    have hK1 : (1 : ℝ) ≤ K n := by exact_mod_cast hK
    have f2 : Real.logb 2 (Λ + 1) + 1 ≤ 4 * (b n : ℝ) ^ (epsilon * cParam) := by
      have := gr_K_le_rpow n
      linarith
    have f12 := gr_mul_le hB (by linarith [gr_logb_nonneg (show (1 : ℝ) ≤ Λ + 1 by linarith)])
      (by norm_num) f1 f2
    have := gr_le_rpow_of_le hB1 (by norm_num) f12 hll
    linarith
  have hsum : (d n : ℝ) * K n + (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) +
      (ℓ n : ℝ) * (d n : ℝ) ^ totLam' + grLogLog ((r n : ℝ) * p n) ≤
        65 * (b n : ℝ) ^ (1 - totKappa) := by linarith
  have hTp := gr_Tp_le h.1
  unfold totConv
  calc _ ≤ (48 * n) * (65 * (b n : ℝ) ^ (1 - totKappa)) :=
        mul_le_mul hTp hsum (tot_conv_inner_nonneg h) (by positivity)
    _ = 3120 * ((n : ℝ) * (b n : ℝ) ^ (1 - totKappa)) := by ring

theorem tot_conv_nonneg (h : Big n) : 0 ≤ totConv n :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (tot_conv_inner_nonneg h)

end Terms

/-! ### The total -/

/-- The regime of the term bounds: `Big n`, `K ≥ 1`, `log₂ p ≤ K`, `B^C ≤ n`, `n ≥ 8`. -/
theorem tot_eventually (C : ℕ) :
    ∀ᶠ n in atTop, Big n ∧ 1 ≤ K n ∧ Real.logb 2 (p n) ≤ K n ∧
      (b n : ℝ) ^ C ≤ n ∧ 8 ≤ n := by
  filter_upwards [eventually_big, gr_one_le_K, eventually_logb_p_le_K 1, gr_pow_b_le C,
    eventually_ge_atTop 8] with n h1 h2 h3 h4 h5
  rw [one_mul] at h3
  exact ⟨h1, h2, h3, h4, h5⟩

/-- `0 ≤ totBound C n ≤ 40000 C n B^{1-κ}` for all large `n`. -/
theorem tot_le
    (hCRT : epsilon * (2 - Parameters.tau) + Parameters.tau ≤ 1 - totKappa) (C : ℕ) :
    ∀ᶠ n in atTop, 0 ≤ totBound C n ∧
      totBound C n ≤ 40000 * C * ((n : ℝ) * (b n : ℝ) ^ (1 - totKappa)) := by
  filter_upwards [tot_eventually C, eventually_clog_p_le_K 1] with n ⟨h, hK, hlog, hbC, _⟩ hclog
  rw [one_mul] at hclog
  obtain ⟨he0, -⟩ := tot_exp_facts
  have hB1 := tot_one_le_b h
  have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hBe : 1 ≤ (b n : ℝ) ^ (1 - totKappa) := Real.one_le_rpow hB1 he0
  have hW : (n : ℝ) ≤ (n : ℝ) * (b n : ℝ) ^ (1 - totKappa) := le_mul_of_one_le_right hN hBe
  have hcrt := tot_crt_le hCRT h
  have hres := tot_resamp_le h hK hclog
  have hconv := tot_conv_le h hK hlog
  have hmp := tot_mp_le h
  have hS : (S n : ℝ) * totMp n ≤ (T n : ℝ) * totMp n := by
    have : (S n : ℝ) ≤ T n := by exact_mod_cast h.S_lt_T.le
    exact mul_le_mul_of_nonneg_right this (tot_mp_nonneg n)
  have hTp := gr_Tp_le h.1
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have h0 : 0 ≤ (n : ℝ) + 2 * totCRT n + 3 * (totResamp n + totConv n + T n * totMp n) +
      T n * totMp n + S n * totMp n + T n * p n + ((n : ℝ) + (b n : ℝ) ^ C) := by
    have c := @Nat.cast_nonneg ℝ _
    have a1 := tot_conv_nonneg h
    have a2 : 0 ≤ totCRT n :=
      mul_nonneg (mul_nonneg (mul_nonneg (c _) (c _)) (pow_nonneg (c _) 2))
        (add_nonneg zero_le_one (Real.rpow_nonneg (c _) _))
    have a3 : 0 ≤ totResamp n :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (c _) (c _)) (Real.rpow_nonneg (c _) _))
        (c _)) (tot_mp_nonneg n)
    have a4 : 0 ≤ (T n : ℝ) * totMp n := mul_nonneg (c _) (tot_mp_nonneg n)
    have a5 : 0 ≤ (S n : ℝ) * totMp n := mul_nonneg (c _) (tot_mp_nonneg n)
    have a6 : 0 ≤ (T n : ℝ) * p n := mul_nonneg (c _) (c _)
    have a7 : 0 ≤ (b n : ℝ) ^ C := pow_nonneg (c _) _
    linarith
  refine ⟨mul_nonneg hC h0, ?_⟩
  unfold totBound
  have hsum : (n : ℝ) + 2 * totCRT n + 3 * (totResamp n + totConv n + T n * totMp n) +
      T n * totMp n + S n * totMp n + T n * p n + ((n : ℝ) + (b n : ℝ) ^ C) ≤
        40000 * ((n : ℝ) * (b n : ℝ) ^ (1 - totKappa)) := by
    have : 0 ≤ (n : ℝ) * (b n : ℝ) ^ (1 - totKappa) := by positivity
    linarith
  calc (C : ℝ) * _ ≤ C * (40000 * ((n : ℝ) * (b n : ℝ) ^ (1 - totKappa))) :=
        mul_le_mul_of_nonneg_left hsum hC
    _ = 40000 * C * ((n : ℝ) * (b n : ℝ) ^ (1 - totKappa)) := by ring

/-- **The total-time bound**: `totBound C = O(n (log n)^{1-κ})` at `κ = totKappa`. -/
theorem totBound_isBigO_kappa
    (hCRT : epsilon * (2 - Parameters.tau) + Parameters.tau ≤ 1 - totKappa) (C : ℕ) :
    (fun n => totBound C n) =O[atTop] fun n : ℕ => (n : ℝ) * Real.log n ^ (1 - totKappa) := by
  have h1 : (fun n => totBound C n) =O[atTop]
      fun n : ℕ => (n : ℝ) * (b n : ℝ) ^ (1 - totKappa) := by
    apply IsBigO.of_bound (40000 * C)
    filter_upwards [tot_le hCRT C] with n ⟨h0, h⟩
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by positivity)]
    exact h
  exact h1.trans (gr_isBigO_b_rpow tot_exp_facts.1)

/-- **The total-time bound**: `totBound C = O(n (log n)^{1-κ})` for some `κ > 0`. -/
theorem totBound_isBigO
    (hCRT : epsilon * (2 - Parameters.tau) + Parameters.tau ≤ 1 - totKappa) (C : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧
      (fun n => totBound C n) =O[atTop] fun n : ℕ => (n : ℝ) * Real.log n ^ (1 - κ) :=
  ⟨totKappa, tot_kappa_pos, totBound_isBigO_kappa hCRT C⟩

/-- **The hypothesis `htime` of `Fast.statement_of_dispatch`** at `κ = totKappa`, for an
`ℕ`-valued `time` bounded by `totBound C` for all large `n`. -/
theorem tot_htime
    (hCRT : epsilon * (2 - Parameters.tau) + Parameters.tau ≤ 1 - totKappa) (C : ℕ)
    {time : ℕ → ℕ} (h : ∀ᶠ n in atTop, (time n : ℝ) ≤ totBound C n) :
    (fun n => (time n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) * Real.log n ^ (1 - totKappa) := by
  have h1 : (fun n => (time n : ℝ)) =O[atTop] fun n => totBound C n := by
    apply IsBigO.of_bound 1
    filter_upwards [h, tot_le hCRT C] with n hn ⟨h0, _⟩
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg h0, one_mul]
    exact hn
  exact h1.trans (totBound_isBigO_kappa hCRT C)

end IntegerMultBounds.MathlibTM2.Cost
