module

public import IntegerMultBounds.MathlibTM2.Layer.Recurrence
public import IntegerMultBounds.MathlibTM2.Layer.SelectedMoments

/-!
# The closed layer recurrence for variable-rank child calls

`Layer.Recurrence.recurrence_closed` bounds a node whose `s` children all have size `e/m`,
from the scalar branching `a = s/W` with `log_m a < λ`. A variable-rank supplier makes
child calls of different sizes `r_i e/m` at one node, so its branching enters only as an
occurrence moment `Σ_i w_i (r_i/m)^λ`. This file proves the variable-rank form of the closed
recurrence, with the same per-node overhead `C₁ ((K e)^τ + 1)` and the same leaf term:

* `variable_closed`: if every internal node costs at most `C₁ ((K e)^τ + 1)` plus the weighted
  costs of its child occurrences, leaves of size `e ≤ u` cost at most `C₀ e`, the moments
  satisfy `Σ w (r/m)^λ ≤ q < 1` and `Σ w (r/m)^σ ≤ 1`, then every node costs at most
  `2 C₁/(1-q) · K^τ e^λ + C₀ e^σ u^(1-σ)`. This is `recurrence_closed` with `leaf_le`, without
  the uniform level structure.
* `moment_lam_le`, `moment_lam_lt_one`: a moment at `σ` bounded by one and ranks at most
  `R < m` give a strict moment `((R/m)^(λ-σ)) < 1` at every `λ > σ`.
* `t16_variable_closed`: the instance with the selected T16 occurrence list (`m = 73`,
  weight `1/14336`, ranks at most `48`) at `σ = 1 - 7/4178` and any `λ > σ`.

The node type, child map, sizes and costs are the caller's: as in
`Layer.OccurrenceRecurrence`, nothing here constructs or hosts the selected supplier, and the
size relation `size (child) ≤ (rank/m) size` is an execution premise.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer.VariableRecurrence

open Finset

/-! ### Moments at a larger exponent -/

/-- `x^λ ≤ x^σ y^(λ-σ)` for `0 ≤ x ≤ y` and `0 ≤ σ ≤ λ`. -/
theorem rpow_le_rpow_mul {x y σ lam : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hσ : 0 ≤ σ)
    (hσl : σ ≤ lam) : x ^ lam ≤ x ^ σ * y ^ (lam - σ) := by
  rcases eq_or_lt_of_le (hσ.trans hσl) with h0 | hpos
  · have hσ0 : σ = 0 := le_antisymm (h0 ▸ hσl) hσ
    rw [← h0, hσ0]; simp
  · have e : x ^ lam = x ^ σ * x ^ (lam - σ) := by
      rw [← Real.rpow_add' hx (by rw [add_sub_cancel]; exact hpos.ne')]
      congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy (by linarith))
      (Real.rpow_nonneg hx σ)

/-- Ranks at most `R ≤ m` transfer a moment from `σ` to `λ ≥ σ` at the factor
`(R/m)^(λ-σ)`. -/
theorem moment_lam_le {n : ℕ} (rank : Fin n → ℕ) (weight : Fin n → ℝ) {m R σ lam : ℝ}
    (hm : 0 < m) (hσ : 0 ≤ σ) (hσl : σ ≤ lam) (hweight : ∀ i, 0 ≤ weight i)
    (hrank : ∀ i, (rank i : ℝ) ≤ R) :
    ∑ i, weight i * ((rank i : ℝ) / m) ^ lam ≤
      (R / m) ^ (lam - σ) * ∑ i, weight i * ((rank i : ℝ) / m) ^ σ := by
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  have hx : (0 : ℝ) ≤ (rank i : ℝ) / m := div_nonneg (Nat.cast_nonneg _) hm.le
  have hxy : (rank i : ℝ) / m ≤ R / m := div_le_div_of_nonneg_right (hrank i) hm.le
  calc weight i * ((rank i : ℝ) / m) ^ lam
      ≤ weight i * (((rank i : ℝ) / m) ^ σ * (R / m) ^ (lam - σ)) :=
        mul_le_mul_of_nonneg_left (rpow_le_rpow_mul hx hxy hσ hσl) (hweight i)
    _ = (R / m) ^ (lam - σ) * (weight i * ((rank i : ℝ) / m) ^ σ) := by ring

/-- A moment at most one at `σ`, with ranks at most `R < m`, is strictly below one at every
`λ > σ`: it is at most `(R/m)^(λ-σ) < 1`. -/
theorem moment_lam_lt_one {n : ℕ} (rank : Fin n → ℕ) (weight : Fin n → ℝ) {m R σ lam : ℝ}
    (hm : 0 < m) (hR : 0 ≤ R) (hRm : R < m) (hσ : 0 ≤ σ) (hσl : σ < lam)
    (hweight : ∀ i, 0 ≤ weight i) (hrank : ∀ i, (rank i : ℝ) ≤ R)
    (hmom : ∑ i, weight i * ((rank i : ℝ) / m) ^ σ ≤ 1) :
    ∑ i, weight i * ((rank i : ℝ) / m) ^ lam ≤ (R / m) ^ (lam - σ) ∧
      (R / m) ^ (lam - σ) < 1 := by
  have hq0 : 0 ≤ (R / m) ^ (lam - σ) := Real.rpow_nonneg (div_nonneg hR hm.le) _
  refine ⟨(moment_lam_le rank weight hm hσ hσl.le hweight hrank).trans ?_, ?_⟩
  · calc (R / m) ^ (lam - σ) * ∑ i, weight i * ((rank i : ℝ) / m) ^ σ
        ≤ (R / m) ^ (lam - σ) * 1 := mul_le_mul_of_nonneg_left hmom hq0
      _ = (R / m) ^ (lam - σ) := mul_one _
  · exact Real.rpow_lt_one (div_nonneg hR hm.le) ((div_lt_one hm).2 hRm) (by linarith)

/-! ### The closed recurrence -/

/-- A leaf of size `e ≤ u` with `C₀ e` cost fits `C₀ e^σ u^(1-σ)` for `σ ≤ 1`. -/
theorem leaf_term_le {e u σ : ℝ} (he : 0 ≤ e) (heu : e ≤ u) (hσ1 : σ ≤ 1) :
    e ≤ e ^ σ * u ^ (1 - σ) := by
  rcases eq_or_lt_of_le he with h0 | hpos
  · rw [← h0]
    have : (0 : ℝ) ≤ (0 : ℝ) ^ σ * u ^ (1 - σ) :=
      mul_nonneg (Real.rpow_nonneg le_rfl _) (Real.rpow_nonneg (he.trans heu) _)
    exact this
  · calc e = e ^ σ * e ^ (1 - σ) := by
          rw [← Real.rpow_add hpos, add_sub_cancel, Real.rpow_one]
      _ ≤ e ^ σ * u ^ (1 - σ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hpos.le heu (by linarith))
            (Real.rpow_nonneg hpos.le σ)

/-- **Variable-rank recurrence.** Internal nodes (size above the cutoff `u ≥ 1`) cost at most
`C₁ ((K e)^τ + 1)` plus the weighted costs of their child occurrences, whose sizes are at most
`(rank/m) e` and strictly smaller; leaves cost at most `C₀ e`. If every internal node has
`Σ w (r/m)^λ ≤ q < 1` and `Σ w (r/m)^σ ≤ 1`, with `0 ≤ τ ≤ λ`, `0 ≤ σ ≤ 1` and `K ≥ 1`, then
every node costs at most `2 C₁/(1-q) · K^τ e^λ + C₀ e^σ u^(1-σ)`. -/
theorem variable_closed {Node : Type*}
    (size : Node → ℕ) (arity : Node → ℕ)
    (child : (x : Node) → Fin (arity x) → Node)
    (rank : (x : Node) → Fin (arity x) → ℕ)
    (weight : (x : Node) → Fin (arity x) → ℝ)
    (cost : Node → ℝ) (u : ℕ) {m τ σ lam K C₀ C₁ q : ℝ}
    (hm : 0 < m) (hτ : 0 ≤ τ) (hτl : τ ≤ lam) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hK : 1 ≤ K)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hq : q < 1) (hu : 1 ≤ u)
    (hweight : ∀ x i, 0 ≤ weight x i)
    (hleaf : ∀ x, size x ≤ u → cost x ≤ C₀ * size x)
    (hdecrease : ∀ x, u < size x → ∀ i, size (child x i) < size x)
    (hsize : ∀ x, u < size x → ∀ i,
      (size (child x i) : ℝ) ≤ ((rank x i : ℝ) / m) * (size x : ℝ))
    (hcost : ∀ x, u < size x →
      cost x ≤ C₁ * ((K * size x) ^ τ + 1) + ∑ i, weight x i * cost (child x i))
    (hmomLam : ∀ x, u < size x → ∑ i, weight x i * ((rank x i : ℝ) / m) ^ lam ≤ q)
    (hmomSigma : ∀ x, u < size x → ∑ i, weight x i * ((rank x i : ℝ) / m) ^ σ ≤ 1) :
    ∀ x, cost x ≤ 2 * C₁ / (1 - q) * K ^ τ * (size x : ℝ) ^ lam +
      C₀ * (size x : ℝ) ^ σ * (u : ℝ) ^ (1 - σ) := by
  set A := 2 * C₁ / (1 - q) with hA
  have hq1 : 0 < 1 - q := by linarith
  have hA0 : 0 ≤ A := div_nonneg (by linarith) hq1.le
  have hlam : 0 ≤ lam := hτ.trans hτl
  have hKτ : 0 ≤ K ^ τ := Real.rpow_nonneg (by linarith) τ
  have hu0 : (0 : ℝ) ≤ (u : ℝ) ^ (1 - σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  intro x
  induction hn : size x using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hsmall : size x ≤ u
    · have h1 := leaf_term_le (Nat.cast_nonneg (size x)) (show (size x : ℝ) ≤ (u : ℝ) by exact_mod_cast hsmall) hσ1
      have h2 : 0 ≤ A * K ^ τ * (size x : ℝ) ^ lam :=
        mul_nonneg (mul_nonneg hA0 hKτ) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have h3 := hleaf x hsmall
      have h4 : C₀ * (size x : ℝ) ≤ C₀ * ((size x : ℝ) ^ σ * (u : ℝ) ^ (1 - σ)) :=
        mul_le_mul_of_nonneg_left h1 hC₀
      rw [← hn]
      nlinarith
    · have hlarge : u < size x := Nat.lt_of_not_ge hsmall
      rw [← hn]
      have hs1 : (1 : ℝ) ≤ size x := by exact_mod_cast (show 1 ≤ size x by omega)
      set s : ℝ := (size x : ℝ) with hs
      -- the children, by induction
      have hchild : ∀ i, cost (child x i) ≤ A * K ^ τ * (size (child x i) : ℝ) ^ lam +
          C₀ * (size (child x i) : ℝ) ^ σ * (u : ℝ) ^ (1 - σ) := fun i =>
        ih _ (hn ▸ hdecrease x hlarge i) (child x i) rfl
      have hlamSum := OccurrenceRecurrence.rank_moment_le (rank x) (fun i => size (child x i))
        (weight x) (Nat.cast_nonneg (size x)) hm hlam (hweight x) (hsize x hlarge)
        (hmomLam x hlarge)
      have hsigSum := OccurrenceRecurrence.rank_moment_le (rank x) (fun i => size (child x i))
        (weight x) (Nat.cast_nonneg (size x)) hm hσ (hweight x) (hsize x hlarge)
        (hmomSigma x hlarge)
      have hsum : ∑ i, weight x i * cost (child x i) ≤
          A * K ^ τ * (q * s ^ lam) + C₀ * (u : ℝ) ^ (1 - σ) * (1 * s ^ σ) := by
        calc ∑ i, weight x i * cost (child x i)
            ≤ ∑ i, weight x i * (A * K ^ τ * (size (child x i) : ℝ) ^ lam +
                C₀ * (size (child x i) : ℝ) ^ σ * (u : ℝ) ^ (1 - σ)) :=
              sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hchild i) (hweight x i)
          _ = A * K ^ τ * ∑ i, weight x i * (size (child x i) : ℝ) ^ lam +
                C₀ * (u : ℝ) ^ (1 - σ) * ∑ i, weight x i * (size (child x i) : ℝ) ^ σ := by
              rw [mul_sum, mul_sum, ← sum_add_distrib]
              apply sum_congr rfl
              intro i _
              ring
          _ ≤ A * K ^ τ * (q * s ^ lam) + C₀ * (u : ℝ) ^ (1 - σ) * (1 * s ^ σ) :=
              add_le_add (mul_le_mul_of_nonneg_left hlamSum (mul_nonneg hA0 hKτ))
                (mul_le_mul_of_nonneg_left hsigSum (mul_nonneg hC₀ hu0))
      have hover : C₁ * ((K * s) ^ τ + 1) ≤ C₁ * (2 * K ^ τ * s ^ lam) :=
        mul_le_mul_of_nonneg_left (Recurrence.overhead_le hK hs1 hτ hτl) hC₁
      have hAq : A * (1 - q) = 2 * C₁ := by rw [hA]; field_simp
      calc cost x ≤ C₁ * ((K * s) ^ τ + 1) + ∑ i, weight x i * cost (child x i) := hcost x hlarge
        _ ≤ C₁ * (2 * K ^ τ * s ^ lam) +
            (A * K ^ τ * (q * s ^ lam) + C₀ * (u : ℝ) ^ (1 - σ) * (1 * s ^ σ)) :=
          add_le_add hover hsum
        _ = A * K ^ τ * s ^ lam + C₀ * s ^ σ * (u : ℝ) ^ (1 - σ) := by
          linear_combination (-(K ^ τ * s ^ lam)) * hAq

/-- The variable-rank recurrence from a single moment bound at `σ` and ranks at most
`R < m`: at every `λ > σ` the contraction is `q = (R/m)^(λ-σ)`. -/
theorem variable_closed_of_rank {Node : Type*}
    (size : Node → ℕ) (arity : Node → ℕ)
    (child : (x : Node) → Fin (arity x) → Node)
    (rank : (x : Node) → Fin (arity x) → ℕ)
    (weight : (x : Node) → Fin (arity x) → ℝ)
    (cost : Node → ℝ) (u : ℕ) {m R τ σ lam K C₀ C₁ : ℝ}
    (hm : 0 < m) (hR : 0 ≤ R) (hRm : R < m) (hτ : 0 ≤ τ) (hτl : τ ≤ lam) (hσ : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hσl : σ < lam) (hK : 1 ≤ K) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hu : 1 ≤ u)
    (hweight : ∀ x i, 0 ≤ weight x i)
    (hrank : ∀ x, u < size x → ∀ i, (rank x i : ℝ) ≤ R)
    (hleaf : ∀ x, size x ≤ u → cost x ≤ C₀ * size x)
    (hsize : ∀ x, u < size x → ∀ i,
      (size (child x i) : ℝ) ≤ ((rank x i : ℝ) / m) * (size x : ℝ))
    (hcost : ∀ x, u < size x →
      cost x ≤ C₁ * ((K * size x) ^ τ + 1) + ∑ i, weight x i * cost (child x i))
    (hmom : ∀ x, u < size x → ∑ i, weight x i * ((rank x i : ℝ) / m) ^ σ ≤ 1) :
    ∀ x, cost x ≤ 2 * C₁ / (1 - (R / m) ^ (lam - σ)) * K ^ τ * (size x : ℝ) ^ lam +
      C₀ * (size x : ℝ) ^ σ * (u : ℝ) ^ (1 - σ) := by
  have hq : (R / m) ^ (lam - σ) < 1 :=
    Real.rpow_lt_one (div_nonneg hR hm.le) ((div_lt_one hm).2 hRm) (by linarith)
  have decrease (x) (hx : u < size x) (i) : size (child x i) < size x := by
    have pos : (0 : ℝ) < size x := by exact_mod_cast (Nat.zero_lt_of_lt hx)
    have ratio := (div_lt_one hm).2 ((hrank x hx i).trans_lt hRm)
    exact_mod_cast (hsize x hx i).trans_lt (mul_lt_of_lt_one_left pos ratio)
  exact variable_closed size arity child rank weight cost u hm hτ hτl hσ hσ1 hK hC₀ hC₁ hq hu
    hweight hleaf decrease hsize hcost
    (fun x hx => (moment_lam_lt_one (rank x) (weight x) hm hR hRm hσ hσl (hweight x)
      (hrank x hx) (hmom x hx)).1)
    hmom

/-! ### The selected T16 instance -/

section T16

open SelectedMoments

/-- Every T16 child rank is at most `48`. -/
theorem t16Ranks_le (i : Fin t16Ranks.length) : t16Ranks[i.1] ≤ 48 := by
  have hmem : t16Ranks[i.1] ∈ t16Ranks := List.getElem_mem i.2
  have hperm := t16Ranks_realizes.mem_iff.1 hmem
  simp only [expand, complexHistogram, List.flatMap_cons, List.flatMap_nil, List.mem_append,
    List.mem_replicate, List.not_mem_nil, or_false] at hperm
  omega

/-- **T16 layer recurrence.** A layer machine whose internal nodes make one child call per
T16 occurrence, of size at most `rank/73` of the parent and weight `1/14336`, with per-node
overhead `C₁ ((K e)^τ + 1)` and leaf cost `C₀ e`, costs at most
`C (K^τ e^λ) + C₀ e^(1-a) u^a` at every `λ > 1 - a`, `a = 7/4178`. The execution premises
(`hsize`, `hcost`) are the open hosting obligations of the selected supplier. -/
theorem t16_variable_closed {Node : Type*}
    (size : Node → ℕ) (child : Node → Fin t16Ranks.length → Node)
    (cost : Node → ℝ) (u : ℕ) {τ lam K C₀ C₁ : ℝ}
    (hτ : 0 ≤ τ) (hτl : τ ≤ lam) (hlam : 1 - complexSaving < lam) (hK : 1 ≤ K)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hu : 1 ≤ u)
    (hleaf : ∀ x, size x ≤ u → cost x ≤ C₀ * size x)
    (hsize : ∀ x, u < size x → ∀ i,
      (size (child x i) : ℝ) ≤ ((t16Ranks[i.1] : ℝ) / 73) * (size x : ℝ))
    (hcost : ∀ x, u < size x →
      cost x ≤ C₁ * ((K * size x) ^ τ + 1) + ∑ i, (1 / (14336 : ℝ)) * cost (child x i)) :
    ∀ x, cost x ≤
      2 * C₁ / (1 - ((48 : ℝ) / 73) ^ (lam - (1 - complexSaving))) * K ^ τ *
        (size x : ℝ) ^ lam +
      C₀ * (size x : ℝ) ^ (1 - complexSaving) * (u : ℝ) ^ (1 - (1 - complexSaving)) := by
  have ha : complexSaving = 7 / 4178 := rfl
  exact variable_closed_of_rank size (fun _ => t16Ranks.length) child
    (fun _ i => t16Ranks[i.1]) (fun _ _ => 1 / (14336 : ℝ)) cost u (m := 73) (R := 48)
    (by norm_num) (by norm_num) (by norm_num) hτ hτl (by rw [ha]; norm_num)
    (by rw [ha]; norm_num) hlam hK hC₀ hC₁ hu (fun _ _ => by norm_num)
    (fun _ _ i => by exact_mod_cast t16Ranks_le i) hleaf hsize hcost
    (fun _ _ => t16_occurrence_moment_le)

end T16

end IntegerMultBounds.MathlibTM2.Layer.VariableRecurrence
