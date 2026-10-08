import IntegerMultBounds.Sizes

/-! The cost table of §8. Each operation's cost divided by the padded volume
`V = T p` is a product of the size parameters `d`, `K`, `ℓ`, `α` and powers of
`p`; the size relations turn every row into a fixed multiple of `p^(1 - g_i)`
for the witness margin `g_i` of `Parameters.margin`. The seven rows then feed
the assembly of `TimeBound`: a total cost bounded by the table, polynomial
setup, and bounded overheads is `O(n (lg n)^(1 - κ))`. The rows follow the
witness margins: prefix moves `d K`, chunk exchanges `p K^(τ-1)`, simultaneous
rounds `ℓ d^λ'`, axis layouts `d (1 + ℓ^τ)`, Gaussian line maps
`d p^(1/2+δ) α` with `α = ⌈(12 d b)^(1/4)⌉`, chirps `d p^δ`, and packed
products `log (r p)`. That the components achieve these rows is their own
obligation. -/

namespace IntegerMultBounds.CostTable

open Filter Parameters Machine TimeBound Sizes

theorem margin_zero : margin 0 = 1 - epsilon * (1 + spacing) := rfl
theorem margin_one : margin 1 = epsilon * spacing * (1 - tau) := rfl
theorem margin_two : margin 2 = epsilon * (1 - lam') := rfl
theorem margin_three : margin 3 = (1 - tau) * (1 - epsilon) := rfl
theorem margin_four : margin 4 = 1 / 4 - delta - 5 * epsilon / 4 := rfl
theorem margin_five : margin 5 = 1 - delta - epsilon := rfl
theorem margin_six : margin 6 = epsilon := rfl

theorem tau_lt_one : tau < 1 := by norm_num [tau]
theorem tau_pos : 0 < tau := by norm_num [tau]
theorem lam'_lt_one : lam' < 1 := by norm_num [lam']
theorem delta_pos : 0 < delta := by norm_num [delta]
theorem epsilon_lt_one : epsilon < 1 := by norm_num [epsilon]

section Helpers

/-- A negative power is antitone in its base. -/
theorem rpow_neg_le {x L e : ℝ} (hL : 0 < L) (hx : L ≤ x) (he : 0 ≤ e) :
    x ^ (-e) ≤ L ^ (-e) := by
  rw [Real.rpow_neg (hL.trans_le hx).le, Real.rpow_neg hL.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hL e) (Real.rpow_le_rpow hL.le hx he)

theorem div_rpow_neg {L c e : ℝ} (hL : 0 ≤ L) (hc : 0 < c) :
    (L / c) ^ (-e) = c ^ e * L ^ (-e) := by
  rw [Real.rpow_neg (div_nonneg hL hc.le), Real.div_rpow hL hc.le, inv_div, Real.rpow_neg hL,
    div_eq_mul_inv]

theorem one_le_precision (n : ℕ) : 1 ≤ precision n := by linarith [six_le_precision n]

/-- Eventually `ℓ ≤ 4 p^(1-ε)`. -/
theorem eventually_ℓ_le : ∀ᶠ n : ℕ in atTop, (ℓ n : ℝ) ≤ 4 * precision n ^ (1 - epsilon) := by
  filter_upwards [eventually_ℓ_bounds, eventually_d_ge] with n ⟨_, hhi⟩ hd
  have hp := precision_pos n
  have hpe : 0 < precision n ^ epsilon := Real.rpow_pos_of_pos hp _
  have hd0 : 0 < (d n : ℝ) := by exact_mod_cast one_le_d n
  calc (ℓ n : ℝ) ≤ precision n / (3 * d n) := hhi
    _ ≤ precision n / (3 * (precision n ^ epsilon / 12)) :=
        div_le_div_of_nonneg_left hp.le (by positivity) (by linarith)
    _ = 4 * (precision n / precision n ^ epsilon) := by field_simp; ring
    _ = 4 * precision n ^ (1 - epsilon) := by rw [Real.rpow_sub hp, Real.rpow_one]

end Helpers

section Rows

/-- Prefix-slot moves and individual butterfly rounds: `d K`. -/
noncomputable def prefixMoves (n : ℕ) : ℝ := d n * K n

theorem prefixMoves_le (n : ℕ) : prefixMoves n ≤ precision n ^ (1 - margin 0) := by
  unfold prefixMoves
  have hp := precision_pos n
  rw [margin_zero, show (1 : ℝ) - (1 - epsilon * (1 + spacing)) = epsilon + epsilon * spacing by
    ring, Real.rpow_add hp]
  exact mul_le_mul (d_le n) (K_le n) (by positivity) (Real.rpow_nonneg hp.le _)

/-- Chunk exchanges for the transform layout: `p K^(τ-1)`. -/
noncomputable def chunkExchanges (n : ℕ) : ℝ := precision n * (K n : ℝ) ^ (tau - 1)

theorem chunkExchanges_le :
    ∀ᶠ n : ℕ in atTop, chunkExchanges n ≤ 24 ^ (1 - tau) * precision n ^ (1 - margin 1) := by
  filter_upwards [eventually_K_ge] with n hK
  unfold chunkExchanges
  have hp := precision_pos n
  have hpe : 0 < precision n ^ (epsilon * spacing) := Real.rpow_pos_of_pos hp _
  have h1τ : 0 ≤ 1 - tau := by linarith [tau_lt_one]
  have hKpow : (K n : ℝ) ^ (tau - 1) ≤ (precision n ^ (epsilon * spacing) / 24) ^ (-(1 - tau)) := by
    rw [show tau - 1 = -(1 - tau) by ring]
    exact rpow_neg_le (by positivity) hK h1τ
  have hsplit : (precision n ^ (epsilon * spacing) / 24) ^ (-(1 - tau)) =
      24 ^ (1 - tau) * precision n ^ (-(epsilon * spacing * (1 - tau))) := by
    rw [div_rpow_neg hpe.le (by norm_num), ← Real.rpow_mul hp.le]
    ring_nf
  calc precision n * (K n : ℝ) ^ (tau - 1)
      ≤ precision n * (24 ^ (1 - tau) * precision n ^ (-(epsilon * spacing * (1 - tau)))) := by
        rw [← hsplit]
        exact mul_le_mul_of_nonneg_left hKpow hp.le
    _ = 24 ^ (1 - tau) * precision n ^ (1 - margin 1) := by
        rw [margin_one, show (1 : ℝ) - epsilon * spacing * (1 - tau) =
          1 + -(epsilon * spacing * (1 - tau)) by ring, Real.rpow_add hp, Real.rpow_one]
        ring

/-- Simultaneous butterfly rounds: `ℓ d^λ'`. -/
noncomputable def simultaneousRounds (n : ℕ) : ℝ := ℓ n * (d n : ℝ) ^ lam'

theorem simultaneousRounds_le :
    ∀ᶠ n : ℕ in atTop,
      simultaneousRounds n ≤ 12 ^ (1 - lam') / 3 * precision n ^ (1 - margin 2) := by
  filter_upwards [eventually_ℓ_bounds, eventually_d_ge] with n ⟨_, hhi⟩ hd
  unfold simultaneousRounds
  have hp := precision_pos n
  have hpe : 0 < precision n ^ epsilon := Real.rpow_pos_of_pos hp _
  have hd0 : 0 < (d n : ℝ) := by exact_mod_cast one_le_d n
  have h1l : 0 ≤ 1 - lam' := by linarith [lam'_lt_one]
  have hdpow : (d n : ℝ) ^ lam' = d n * (d n : ℝ) ^ (-(1 - lam')) := by
    rw [Real.rpow_neg hd0.le, show lam' = 1 - (1 - lam') by ring, Real.rpow_sub hd0,
      Real.rpow_one, div_eq_mul_inv]
    ring_nf
  have hneg : (d n : ℝ) ^ (-(1 - lam')) ≤ (precision n ^ epsilon / 12) ^ (-(1 - lam')) :=
    rpow_neg_le (by positivity) hd h1l
  have hsplit : (precision n ^ epsilon / 12) ^ (-(1 - lam')) =
      12 ^ (1 - lam') * precision n ^ (-(epsilon * (1 - lam'))) := by
    rw [div_rpow_neg hpe.le (by norm_num), ← Real.rpow_mul hp.le]
    ring_nf
  calc (ℓ n : ℝ) * (d n : ℝ) ^ lam'
      ≤ precision n / (3 * d n) * (d n * (d n : ℝ) ^ (-(1 - lam'))) := by
        rw [hdpow]
        exact mul_le_mul_of_nonneg_right hhi (by positivity)
    _ = precision n / 3 * (d n : ℝ) ^ (-(1 - lam')) := by field_simp
    _ ≤ precision n / 3 * (12 ^ (1 - lam') * precision n ^ (-(epsilon * (1 - lam')))) := by
        rw [← hsplit]
        exact mul_le_mul_of_nonneg_left hneg (by positivity)
    _ = 12 ^ (1 - lam') / 3 * precision n ^ (1 - margin 2) := by
        rw [margin_two, show (1 : ℝ) - epsilon * (1 - lam') = 1 + -(epsilon * (1 - lam')) by ring,
          Real.rpow_add hp, Real.rpow_one]
        ring

/-- CRT and axis layouts: `d (1 + ℓ^τ)`. -/
noncomputable def axisLayouts (n : ℕ) : ℝ := d n * (1 + (ℓ n : ℝ) ^ tau)

theorem axisLayouts_le :
    ∀ᶠ n : ℕ in atTop, axisLayouts n ≤ (1 + 4 ^ tau) * precision n ^ (1 - margin 3) := by
  filter_upwards [eventually_ℓ_le] with n hℓ
  unfold axisLayouts
  have hp := precision_pos n
  have hp1 := one_le_precision n
  have hd := d_le n
  have hd0 : (0 : ℝ) ≤ d n := by positivity
  have hℓpow : (ℓ n : ℝ) ^ tau ≤ 4 ^ tau * precision n ^ ((1 - epsilon) * tau) := by
    rw [Real.rpow_mul hp.le, ← Real.mul_rpow (by norm_num) (Real.rpow_nonneg hp.le _)]
    exact Real.rpow_le_rpow (by positivity) hℓ tau_pos.le
  have hexp : (1 : ℝ) - margin 3 = epsilon + (1 - epsilon) * tau := by
    rw [margin_three]; ring
  have hmono : precision n ^ epsilon ≤ precision n ^ (1 - margin 3) := by
    rw [hexp]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    have : 0 ≤ (1 - epsilon) * tau := by nlinarith [epsilon_lt_one, tau_pos]
    linarith
  calc (d n : ℝ) * (1 + (ℓ n : ℝ) ^ tau)
      ≤ precision n ^ epsilon * (1 + 4 ^ tau * precision n ^ ((1 - epsilon) * tau)) := by
        gcongr
    _ = precision n ^ epsilon + 4 ^ tau * precision n ^ (1 - margin 3) := by
        rw [hexp, Real.rpow_add hp]
        ring
    _ ≤ (1 + 4 ^ tau) * precision n ^ (1 - margin 3) := by
        have h4 : (0 : ℝ) ≤ 4 ^ tau := by positivity
        nlinarith [hmono]

/-- The resampling width `α = ⌈(12 d b)^(1/4)⌉`. -/
noncomputable def alpha (n : ℕ) : ℕ := ⌈(12 * d n * b n : ℝ) ^ (1 / 4 : ℝ)⌉₊

theorem alpha_le (n : ℕ) : (alpha n : ℝ) ≤ 2 * (12 * d n * b n : ℝ) ^ (1 / 4 : ℝ) := by
  unfold alpha
  have hd : (1 : ℝ) ≤ d n := by exact_mod_cast one_le_d n
  have hb : (1 : ℝ) ≤ b n := by exact_mod_cast one_le_b n
  have hA : (1 : ℝ) ≤ (12 * d n * b n : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by nlinarith) (by norm_num)
  have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ (12 * d n * b n : ℝ) ^ (1 / 4 : ℝ))
  linarith

/-- Gaussian line maps: `d p^(1/2+δ) α`. -/
noncomputable def gaussianLines (n : ℕ) : ℝ := d n * precision n ^ (1 / 2 + delta) * alpha n

theorem gaussianLines_le (n : ℕ) :
    gaussianLines n ≤ 2 * 2 ^ (1 / 4 : ℝ) * precision n ^ (1 - margin 4) := by
  unfold gaussianLines
  have hp := precision_pos n
  have hd := d_le n
  have hd0 : (0 : ℝ) ≤ d n := by positivity
  have hb : (b n : ℝ) = precision n / 6 := by rw [precision_eq]; ring
  have hdb : (12 * d n * b n : ℝ) ≤ 2 * precision n ^ (1 + epsilon) := by
    rw [hb, Real.rpow_add hp, Real.rpow_one]
    nlinarith [hd, hp]
  have hα : (alpha n : ℝ) ≤ 2 * (2 ^ (1 / 4 : ℝ) * precision n ^ ((1 + epsilon) / 4)) := by
    calc (alpha n : ℝ) ≤ 2 * (12 * d n * b n : ℝ) ^ (1 / 4 : ℝ) := alpha_le n
      _ ≤ 2 * (2 * precision n ^ (1 + epsilon)) ^ (1 / 4 : ℝ) := by
          gcongr
      _ = 2 * (2 ^ (1 / 4 : ℝ) * precision n ^ ((1 + epsilon) / 4)) := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hp.le _), ← Real.rpow_mul hp.le]
          ring_nf
  have hexp : (1 : ℝ) - margin 4 = epsilon + (1 / 2 + delta) + (1 + epsilon) / 4 := by
    rw [margin_four]; ring
  calc (d n : ℝ) * precision n ^ (1 / 2 + delta) * alpha n
      ≤ precision n ^ epsilon * precision n ^ (1 / 2 + delta) *
          (2 * (2 ^ (1 / 4 : ℝ) * precision n ^ ((1 + epsilon) / 4))) := by
        gcongr
    _ = 2 * 2 ^ (1 / 4 : ℝ) * (precision n ^ epsilon * precision n ^ (1 / 2 + delta) *
          precision n ^ ((1 + epsilon) / 4)) := by ring
    _ = 2 * 2 ^ (1 / 4 : ℝ) * precision n ^ (1 - margin 4) := by
        rw [hexp, Real.rpow_add hp (epsilon + (1 / 2 + delta)) ((1 + epsilon) / 4),
          Real.rpow_add hp epsilon (1 / 2 + delta)]

/-- Chirps, twists, and scalar products: `d p^δ`. -/
noncomputable def chirps (n : ℕ) : ℝ := d n * precision n ^ delta

theorem chirps_le (n : ℕ) : chirps n ≤ precision n ^ (1 - margin 5) := by
  unfold chirps
  have hp := precision_pos n
  rw [margin_five, show (1 : ℝ) - (1 - delta - epsilon) = epsilon + delta by ring,
    Real.rpow_add hp]
  exact mul_le_mul_of_nonneg_right (d_le n) (Real.rpow_nonneg hp.le _)

/-- Packed polynomial products: `log (r p)`. -/
noncomputable def packedProducts (n : ℕ) : ℝ := Real.log (r n * precision n)

theorem packedProducts_le :
    ∀ᶠ n : ℕ in atTop,
      packedProducts n ≤ (4 * Real.log 2 + 1 / (1 - epsilon)) * precision n ^ (1 - margin 6) := by
  filter_upwards [eventually_ℓ_le] with n hℓ
  unfold packedProducts r
  have hp := precision_pos n
  have h1ε : 0 < 1 - epsilon := by linarith [epsilon_lt_one]
  rw [Real.log_mul (by positivity) hp.ne', Real.log_pow, margin_six]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogp : Real.log (precision n) ≤ precision n ^ (1 - epsilon) / (1 - epsilon) :=
    Real.log_le_rpow_div hp.le h1ε
  have h1 : (ℓ n : ℝ) * Real.log 2 ≤ 4 * Real.log 2 * precision n ^ (1 - epsilon) := by
    nlinarith [hℓ, hlog2]
  calc (ℓ n : ℝ) * Real.log 2 + Real.log (precision n)
      ≤ 4 * Real.log 2 * precision n ^ (1 - epsilon) + precision n ^ (1 - epsilon) / (1 - epsilon) := by
        linarith
    _ = (4 * Real.log 2 + 1 / (1 - epsilon)) * precision n ^ (1 - epsilon) := by ring

end Rows

section Assembly

/-- The seven normalized rows of the cost table. -/
noncomputable def tableRows (n : ℕ) : ℝ :=
  prefixMoves n + chunkExchanges n + simultaneousRounds n + axisLayouts n + gaussianLines n +
    chirps n + packedProducts n

/-- The constants in front of `p^(1 - margin i)`. -/
noncomputable def tableConstants : Fin 7 → ℝ
  | 0 => 1
  | 1 => 24 ^ (1 - tau)
  | 2 => 12 ^ (1 - lam') / 3
  | 3 => 1 + 4 ^ tau
  | 4 => 2 * 2 ^ (1 / 4 : ℝ)
  | 5 => 1
  | 6 => 4 * Real.log 2 + 1 / (1 - epsilon)

theorem tc0 : tableConstants 0 = 1 := rfl
theorem tc1 : tableConstants 1 = 24 ^ (1 - tau) := rfl
theorem tc2 : tableConstants 2 = 12 ^ (1 - lam') / 3 := rfl
theorem tc3 : tableConstants 3 = 1 + 4 ^ tau := rfl
theorem tc4 : tableConstants 4 = 2 * 2 ^ (1 / 4 : ℝ) := rfl
theorem tc5 : tableConstants 5 = 1 := rfl
theorem tc6 : tableConstants 6 = 4 * Real.log 2 + 1 / (1 - epsilon) := rfl

theorem tableConstants_nonneg : ∀ i, 0 ≤ tableConstants i
  | 0 => zero_le_one
  | 1 => by rw [tc1]; positivity
  | 2 => by rw [tc2]; positivity
  | 3 => by rw [tc3]; positivity
  | 4 => by rw [tc4]; positivity
  | 5 => zero_le_one
  | 6 => by
      rw [tc6]
      have h1ε : 0 < 1 - epsilon := by linarith [epsilon_lt_one]
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      positivity

/-- Every row of the table is eventually its constant times `p^(1 - margin i)`. -/
theorem tableRows_le :
    ∀ᶠ n : ℕ in atTop, tableRows n ≤ ∑ i, tableConstants i * precision n ^ (1 - margin i) := by
  filter_upwards [chunkExchanges_le, simultaneousRounds_le, axisLayouts_le, packedProducts_le]
    with n h1 h2 h3 h6
  have h0 := prefixMoves_le n
  have h4 := gaussianLines_le n
  have h5 := chirps_le n
  rw [Fin.sum_univ_seven, tc0, tc1, tc2, tc3, tc4, tc5, tc6, one_mul, one_mul]
  unfold tableRows
  linarith

/-- The complete time bound from the cost table: a total cost at most the volume
times the table rows, plus polynomial setup and bounded overheads, is
`O(n (lg n)^(1 - κ))` with `κ = 83 / 10^12`. -/
theorem table_time_bound (V : ℕ → ℝ) (cV : ℝ) (hV0 : ∀ n, 0 ≤ V n) (hV : ∀ n, V n ≤ cV * n)
    (setup : List (ℝ × ℝ)) (hsetup : ∀ s ∈ setup, 0 ≤ s.1 ∧ 0 ≤ s.2)
    (bounded : List (ℝ × (ℝ → ℝ) × ℝ))
    (hbounded : ∀ b ∈ bounded, 0 ≤ b.1 ∧ 0 ≤ b.2.2 ∧ ∀ᶠ p in atTop, b.2.1 p ≤ b.2.2)
    (total : ℕ → ℝ)
    (htotal : ∀ᶠ n : ℕ in atTop, total n ≤ V n * tableRows n +
      (setup.map fun s => s.1 * precision n ^ s.2).sum +
      (bounded.map fun b => b.1 * V n * b.2.1 (precision n)).sum) :
    ∃ (C : ℝ) (n₀ : ℕ), 0 < C ∧ ∀ n, n₀ ≤ n → total n ≤ C * targetTime (83 / 10 ^ 12) n := by
  apply multiplication_time_bound V cV hV0 hV tableConstants (fun _ => 0) tableConstants_nonneg
    (fun _ => le_rfl) setup hsetup bounded hbounded total
  filter_upwards [htotal, tableRows_le] with n h1 h2
  have hrows : ((assemblyRows tableConstants fun _ => 0).map fun r =>
      r.cost (V n) (precision n)).sum = V n * ∑ i, tableConstants i * precision n ^ (1 - margin i) := by
    unfold assemblyRows
    rw [List.map_ofFn, List.sum_ofFn, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Function.comp, Row.cost, Real.rpow_zero, mul_one]
    ring
  have := mul_le_mul_of_nonneg_left h2 (hV0 n)
  rw [hrows]
  linarith

end Assembly

end IntegerMultBounds.CostTable
