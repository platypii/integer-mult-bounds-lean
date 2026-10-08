import IntegerMultBounds.CostTable
import IntegerMultBounds.NLogN.ResamplingNumeric
import Mathlib.GroupTheory.Perm.Fin

/-! The transform layout and its cost (§6, Lemma "Transform layout and cost").
The layout moves at most `D (b + 1) ≤ d K` named slots to a prefix, reorders
the `D q` remaining width-`K` chunks with at most `D q - 1` chunk exchanges
(any permutation of `n` positions is a product of at most `n - 1`
transpositions), and runs `1 + qK + b = ℓ` butterfly rounds; the round on a
chunk group sees the complete address set `[P] × [2^K]^D × [S]` of `M` records.
Each round is a contraction followed by one truncation, so `m` rounds have
error at most `m √2 2^(-p)` and keep the disk. The cost bracket
`dK + pK^(τ-1) + ℓ d^λ' + log(rp)` is exactly the sum of four rows of the
cost table of §8, and the lemma's hypothesis `K ≤ ℓ - 1` holds under the size
relations for all large `n`. Tape execution is not part of this file. -/

namespace IntegerMultBounds.LayoutCost

open Equiv Filter Topology Parameters TimeBound Sizes CostTable NLogN

/-! ### Every permutation is a product of at most `n - 1` transpositions -/

section Swaps

variable {n : ℕ}

/-- Extend a permutation of `Fin n` to `Fin (n + 1)` fixing `0`. -/
def extend (e : Perm (Fin n)) : Perm (Fin (n + 1)) := Perm.decomposeFin.symm (0, e)

@[simp] theorem extend_zero (e : Perm (Fin n)) : extend e 0 = 0 :=
  Perm.decomposeFin_symm_apply_zero 0 e

@[simp] theorem extend_succ (e : Perm (Fin n)) (x : Fin n) : extend e x.succ = (e x).succ := by
  rw [extend, Perm.decomposeFin_symm_apply_succ, swap_self]
  rfl

theorem extend_one : extend (1 : Perm (Fin n)) = 1 := by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ x => simp

theorem extend_mul (e₁ e₂ : Perm (Fin n)) : extend (e₁ * e₂) = extend e₁ * extend e₂ := by
  ext i
  cases i using Fin.cases with
  | zero => simp [Perm.mul_apply]
  | succ x => simp [Perm.mul_apply]

theorem extend_prod (l : List (Perm (Fin n))) : extend l.prod = (l.map extend).prod := by
  induction l with
  | nil => simp [extend_one]
  | cons e l ih => simp [extend_mul, ih]

theorem extend_swap (a b : Fin n) : extend (swap a b) = swap a.succ b.succ := by
  ext i
  cases i using Fin.cases with
  | zero =>
    rw [extend_zero, swap_apply_of_ne_of_ne (Fin.succ_ne_zero a).symm (Fin.succ_ne_zero b).symm]
  | succ x =>
    rw [extend_succ]
    by_cases hxa : x = a
    · subst hxa
      simp
    by_cases hxb : x = b
    · subst hxb
      simp
    rw [swap_apply_of_ne_of_ne hxa hxb,
      swap_apply_of_ne_of_ne (fun h => hxa (Fin.succ_injective _ h))
        (fun h => hxb (Fin.succ_injective _ h))]

theorem extend_isSwap {τ : Perm (Fin n)} (h : τ.IsSwap) : (extend τ).IsSwap := by
  obtain ⟨a, b, hab, rfl⟩ := h
  exact ⟨a.succ, b.succ, fun h => hab (Fin.succ_injective _ h), extend_swap a b⟩

/-- `σ = swap 0 (σ 0) · extend e` with `e` the residual permutation. -/
theorem decompose (σ : Perm (Fin (n + 1))) :
    σ = swap 0 (Perm.decomposeFin σ).1 * extend (Perm.decomposeFin σ).2 := by
  conv_lhs => rw [← Perm.decomposeFin.symm_apply_apply σ]
  obtain ⟨p, e⟩ := Perm.decomposeFin σ
  ext i
  cases i using Fin.cases with
  | zero => simp [Perm.mul_apply]
  | succ x => simp [Perm.mul_apply, Perm.decomposeFin_symm_apply_succ]

/-- Any permutation of `n` positions is a product of at most `n - 1` transpositions:
the left-to-right exchange scan of the manuscript. -/
theorem exists_swap_list : ∀ (n : ℕ) (σ : Perm (Fin n)),
    ∃ l : List (Perm (Fin n)), (∀ τ ∈ l, τ.IsSwap) ∧ l.prod = σ ∧ l.length ≤ n - 1
  | 0, σ => ⟨[], by simp, Subsingleton.elim _ _, by simp⟩
  | n + 1, σ => by
    obtain ⟨l, hl, hprod, hlen⟩ := exists_swap_list n (Perm.decomposeFin σ).2
    have hσ := decompose σ
    by_cases hp : (Perm.decomposeFin σ).1 = 0
    · refine ⟨l.map extend, ?_, ?_, ?_⟩
      · intro τ hτ
        obtain ⟨τ', hτ', rfl⟩ := List.mem_map.mp hτ
        exact extend_isSwap (hl τ' hτ')
      · rw [← extend_prod, hprod, hσ, hp, swap_self]
        rfl
      · simp only [List.length_map]
        omega
    · refine ⟨swap 0 (Perm.decomposeFin σ).1 :: l.map extend, ?_, ?_, ?_⟩
      · intro τ hτ
        rcases List.mem_cons.mp hτ with rfl | hτ
        · exact ⟨0, _, Ne.symm hp, rfl⟩
        · obtain ⟨τ', hτ', rfl⟩ := List.mem_map.mp hτ
          exact extend_isSwap (hl τ' hτ')
      · rw [List.prod_cons, ← extend_prod, hprod]
        exact hσ.symm
      · simp only [List.length_cons, List.length_map]
        rcases n with _ | n
        · exact absurd (Fin.fin_one_eq_zero _) hp
        · omega

end Swaps

/-! ### Counting slots, chunks, and rounds -/

section Counting

/-- At most `D (b + 1) ≤ d K` named slots move to the prefix. -/
theorem prefix_slots_le {D d b K : ℕ} (hD : D ≤ d) (hb : b < K) : D * (b + 1) ≤ d * K :=
  Nat.mul_le_mul hD hb

/-- The chunk reorder is realized by at most `D q - 1` chunk exchanges. -/
theorem chunk_exchanges_le (D q : ℕ) (σ : Perm (Fin (D * q))) :
    ∃ l : List (Perm (Fin (D * q))), (∀ τ ∈ l, τ.IsSwap) ∧ l.prod = σ ∧ l.length ≤ D * q - 1 :=
  exists_swap_list _ σ

/-- `D q` exchanges of cost `K^τ` each are at most `D ℓ K^(τ-1)`, since `q K ≤ ℓ`. -/
theorem exchange_cost_le {D q K ℓ : ℕ} (hK : 1 ≤ K) (hq : q * K ≤ ℓ) (τ : ℝ) :
    ((D * q : ℕ) : ℝ) * (K : ℝ) ^ τ ≤ (D : ℝ) * ℓ * (K : ℝ) ^ (τ - 1) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hq' : (q : ℝ) * K ≤ ℓ := by exact_mod_cast hq
  rw [Real.rpow_sub_one hK0.ne']
  have h : (0 : ℝ) ≤ (K : ℝ) ^ τ / K := by positivity
  calc ((D * q : ℕ) : ℝ) * (K : ℝ) ^ τ = (D : ℝ) * (q * K) * ((K : ℝ) ^ τ / K) := by
        push_cast
        field_simp
      _ ≤ (D : ℝ) * ℓ * ((K : ℝ) ^ τ / K) := by gcongr

/-- With `ℓ - 1 = q K + b`, the leading round, the `q K` chunk rounds, and the `b`
prefix rounds make exactly `ℓ` rounds. -/
theorem rounds_eq {ℓ K : ℕ} (hK : 1 ≤ K) (hℓ : 1 ≤ ℓ) :
    1 + (ℓ - 1) / K * K + (ℓ - 1) % K = ℓ := by
  have := Nat.div_add_mod (ℓ - 1) K
  have hK0 : 0 < K := hK
  rw [mul_comm] at this
  omega

/-- The round on a chunk group sees `P · 2^(DK) · S = 2^(n_P + DK + n_S)` records. -/
theorem record_count (nP D K nS : ℕ) :
    (2 : ℕ) ^ nP * 2 ^ (D * K) * 2 ^ nS = 2 ^ (nP + D * K + nS) := by
  rw [pow_add, pow_add]

/-- The nine descriptor codes `|Γ(v)| ≤ 2 log₂ v + 1` total at most `C_desc p`:
with `ℓ + n_P + n_S ≤ C_ℓ p`, `log₂ d, log₂ D ≤ log₂ max{C_ℓ,1} + log₂ p`,
`log₂ K, log₂ (ρ+1), log₂ p ≤ p` and `log₂ w ≤ log₂ C_w + log₂ p`. -/
theorem descriptor_length_le (p Cℓ Cw lp lmax lCw ld lD lK lρ lw ℓ nP nS : ℝ)
    (hp : 1 ≤ p) (hlp : lp ≤ p) (hlp0 : 0 ≤ lp) (hCℓ : 0 ≤ Cℓ) (hCw : 0 ≤ Cw)
    (hlmax : 0 ≤ lmax) (hlmax' : lmax ≤ max Cℓ 1) (hlCw : 0 ≤ lCw) (hlCw' : lCw ≤ Cw)
    (hsum : ℓ + nP + nS ≤ Cℓ * p) (hd : ld ≤ lmax + lp) (hD : lD ≤ lmax + lp)
    (hK : lK ≤ lp) (hρ : lρ ≤ lp) (hw : lw ≤ lCw + lp) :
    (2 * lp + 1) + (2 * ld + 1) + (2 * ℓ + 1) + (2 * lK + 1) + (2 * lw + 1) +
        (2 * lD + 1) + (2 * nP + 1) + (2 * nS + 1) + (2 * lρ + 1) ≤
      32 * (Cℓ + Cw + 1) * p := by
  have h1 : 2 * Cℓ * p + 12 * lp + 4 * lmax + 2 * lCw + 9 ≤ 32 * (Cℓ + Cw + 1) * p := by
    have hm : lmax ≤ Cℓ + 1 := hlmax'.trans (max_le (by linarith) (by linarith))
    nlinarith
  nlinarith

end Counting

/-! ### Error accumulation over the rounds -/

section Rounds

variable {ι : Type*} [Fintype ι] (p : ℕ)

/-- Componentwise truncation moves a vector by less than `√2 2^(-p)`. -/
theorem norm_rdV_sub_le_sqrt (x : ι → ℂ) : ‖rdV p x - x‖ ≤ Real.sqrt 2 / 2 ^ p := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  exact (norm_rhoC_sub_lt p (x i)).le

/-- The exact rounds `x ↦ C_j x`. -/
def exactIter (C : ℕ → (ι → ℂ) →L[ℂ] (ι → ℂ)) (x : ι → ℂ) : ℕ → (ι → ℂ)
  | 0 => x
  | j + 1 => C j (exactIter C x j)

/-- The computed rounds: each contraction followed by one truncation. -/
noncomputable def compIter (C : ℕ → (ι → ℂ) →L[ℂ] (ι → ℂ)) (x : ι → ℂ) : ℕ → (ι → ℂ)
  | 0 => x
  | j + 1 => rdV p (C j (compIter C x j))

/-- `m` truncated contraction rounds have error at most `m √2 2^(-p)`. -/
theorem compIter_error (C : ℕ → (ι → ℂ) →L[ℂ] (ι → ℂ)) (hC : ∀ j, ‖C j‖ ≤ 1) (x : ι → ℂ)
    (m : ℕ) : ‖compIter p C x m - exactIter C x m‖ ≤ m * (Real.sqrt 2 / 2 ^ p) := by
  induction m with
  | zero => simp [compIter, exactIter]
  | succ m ih =>
    simp only [compIter, exactIter]
    set y := C m (compIter p C x m) with hy
    have h1 := norm_rdV_sub_le_sqrt p y
    have h2 : ‖y - C m (exactIter C x m)‖ ≤ m * (Real.sqrt 2 / 2 ^ p) := by
      rw [hy, ← map_sub]
      calc ‖C m (compIter p C x m - exactIter C x m)‖
          ≤ ‖C m‖ * ‖compIter p C x m - exactIter C x m‖ := (C m).le_opNorm _
        _ ≤ 1 * (m * (Real.sqrt 2 / 2 ^ p)) := by gcongr; exact hC m
        _ = m * (Real.sqrt 2 / 2 ^ p) := one_mul _
    calc ‖rdV p y - C m (exactIter C x m)‖
        = ‖(rdV p y - y) + (y - C m (exactIter C x m))‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖rdV p y - y‖ + ‖y - C m (exactIter C x m)‖ := norm_add_le _ _
      _ ≤ Real.sqrt 2 / 2 ^ p + m * (Real.sqrt 2 / 2 ^ p) := add_le_add h1 h2
      _ = (m + 1 : ℕ) * (Real.sqrt 2 / 2 ^ p) := by push_cast; ring

/-- The computed rounds preserve the disk. -/
theorem compIter_disk (C : ℕ → (ι → ℂ) →L[ℂ] (ι → ℂ)) (hC : ∀ j, ‖C j‖ ≤ 1) {x : ι → ℂ}
    (hx : ‖x‖ ≤ 1) (m : ℕ) : ‖compIter p C x m‖ ≤ 1 := by
  induction m with
  | zero => simpa [compIter] using hx
  | succ m ih =>
    simp only [compIter]
    calc ‖rdV p (C m (compIter p C x m))‖ ≤ ‖C m (compIter p C x m)‖ := norm_rdV_le p _
      _ ≤ ‖C m‖ * ‖compIter p C x m‖ := (C m).le_opNorm _
      _ ≤ 1 * 1 := by gcongr; exact hC m
      _ = 1 := one_mul 1

end Rounds

/-! ### The cost bracket and the cost table -/

section Table

/-- The transform cost bracket with the convolution's `log (r p)` is the sum of the
prefix-move, chunk-exchange, simultaneous-round, and packed-product rows. -/
theorem bracket_eq_rows (n : ℕ) :
    (d n : ℝ) * K n + precision n * (K n : ℝ) ^ (tau - 1) + ℓ n * (d n : ℝ) ^ lam' +
        Real.log (r n * precision n) =
      prefixMoves n + chunkExchanges n + simultaneousRounds n + packedProducts n := rfl

theorem axisLayouts_nonneg (n : ℕ) : 0 ≤ axisLayouts n := by
  unfold axisLayouts
  positivity

theorem gaussianLines_nonneg (n : ℕ) : 0 ≤ gaussianLines n := by
  unfold gaussianLines
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (precision_pos n).le _))
    (Nat.cast_nonneg _)

theorem chirps_nonneg (n : ℕ) : 0 ≤ chirps n := by
  unfold chirps
  exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (precision_pos n).le _)

/-- The four transform rows are at most the whole table. -/
theorem rows_le_tableRows (n : ℕ) :
    prefixMoves n + chunkExchanges n + simultaneousRounds n + packedProducts n ≤ tableRows n := by
  unfold tableRows
  linarith [axisLayouts_nonneg n, gaussianLines_nonneg n, chirps_nonneg n]

/-- The lemma's hypothesis `1 ≤ K ≤ ℓ - 1` holds under the size relations for all
large `n`. -/
theorem eventually_K_lt_ℓ : ∀ᶠ n : ℕ in atTop, K n + 1 ≤ ℓ n := by
  have hexp : 0 < 1 - epsilon - epsilon * spacing := by norm_num [epsilon, spacing]
  have ht : Tendsto (fun n : ℕ => precision n ^ (1 - epsilon - epsilon * spacing)) atTop atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_precision
  filter_upwards [eventually_ℓ_bounds, ht.eventually (eventually_ge_atTop 24)] with n hℓ h24
  obtain ⟨hlo, -⟩ := hℓ
  have hp := precision_pos n
  have hd0 : (0 : ℝ) < d n := by exact_mod_cast one_le_d n
  have hd := d_le n
  have hK := K_le n
  have hK1 : (1 : ℝ) ≤ precision n ^ (epsilon * spacing) :=
    Real.one_le_rpow (by linarith [six_le_precision n]) (mul_pos epsilon_pos spacing_pos).le
  -- `p^(1-ε) = p^(1-ε-εc) · p^(εc) ≥ 24 p^(εc) ≥ 12 (p^(εc) + 1)`
  have hsplit : precision n ^ (1 - epsilon) =
      precision n ^ (1 - epsilon - epsilon * spacing) * precision n ^ (epsilon * spacing) := by
    rw [← Real.rpow_add hp]
    ring_nf
  have h1 : 12 * (precision n ^ (epsilon * spacing) + 1) ≤ precision n ^ (1 - epsilon) := by
    rw [hsplit]
    nlinarith
  -- `p^(1-ε) ≤ p / d` since `d ≤ p^ε`
  have h2 : precision n ^ (1 - epsilon) ≤ precision n / d n := by
    rw [le_div_iff₀ hd0]
    calc precision n ^ (1 - epsilon) * d n ≤ precision n ^ (1 - epsilon) * precision n ^ epsilon := by
          gcongr
      _ = precision n := by rw [← Real.rpow_add hp]; simp
  have h3 : (K n : ℝ) + 1 ≤ ℓ n := by
    calc (K n : ℝ) + 1 ≤ precision n ^ (epsilon * spacing) + 1 := by linarith
      _ ≤ precision n ^ (1 - epsilon) / 12 := by linarith
      _ ≤ precision n / d n / 12 := by gcongr
      _ = precision n / (12 * d n) := by ring
      _ ≤ ℓ n := hlo
  exact_mod_cast h3

end Table

end IntegerMultBounds.LayoutCost
