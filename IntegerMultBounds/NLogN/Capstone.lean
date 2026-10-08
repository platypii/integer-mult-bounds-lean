import IntegerMultBounds.NLogN.CostFinal
import IntegerMultBounds.NLogN.ContractFinal

/-! The capstone of the `O(n log n)` subroutine: correctness and cost of the
explicit recursive step at one common threshold.

For the paper's dimension `d = 1729` and every `n ≥ N₀ := 2^(2^(1000 · 1729³))`
a power-of-two grid `tOf n` and odd pairwise coprime moduli `sOf n` are chosen
once and for all (by `Classical.choose` from `exists_step_data`, which repeats
the elementary grid and moduli construction of `ModuliConstruction`). Then:

* `nlogn_capstone_correct`: the explicit recursive step with these grids and
  moduli (`recursiveStepOutputS`, the paper's windows) computes the exact
  product of any two `n`-bit inputs whenever the per-level rounding oracles are
  within `2^(−p)`.
* `nlogn_capstone_cost`: any cost `M` that above `N₀` is at most one full
  recursive step on these grids and moduli (three convolution pipelines whose
  delegated `3rp`-bit products cost `M`, plus the resampling maps with the
  weight evaluations costed by `expCost` and the small products by `Mcost₀`)
  plus a linear overhead, and below `N₀` is at most the plain multiplier's
  `4·10^6 n (log₂ n)³`, satisfies `M n ≤ D n log n` for all `n ≥ 2`.
* `nlogn_capstone`: both together.

`joint_cost_nlogn_at` is the recurrence closure at an arbitrary threshold
`2^(2^k)` with `k ≥ 624`, which is what lets the cost statement use the
correctness threshold. Nothing beyond the threshold and the oracle bounds is
assumed. Tape steps are not modelled. -/

namespace IntegerMultBounds.NLogN

/-- The recurrence closure at an arbitrary threshold `2^(2^k)`, `k ≥ 624`: the
proof of `joint_cost_nlogn'` with the literal `624` replaced by `k`. The grid and
moduli facts are only needed above the threshold. -/
theorem joint_cost_nlogn_at (k : ℕ) (hk : 624 ≤ k) (M Msmall Ecost : ℕ → ℕ) (K₀ K₁ C : ℕ)
    (s t : ℕ → Fin 1729 → ℕ)
    (ht : ∀ n, 2 ^ (2 ^ k) ≤ n → ∀ i, 0 < t n i)
    (hst : ∀ n, 2 ^ (2 ^ k) ≤ n → ∀ i, s n i ≤ t n i)
    (hT : ∀ n, 2 ^ (2 ^ k) ≤ n → ∏ j, t n j = transformSize n)
    (hE : ∀ q, 16 ≤ q → Ecost q ≤ K₀ * q * (Nat.log 2 q) ^ 4)
    (hM₀ : ∀ q, 2 ≤ q → Msmall q ≤ K₁ * q * (Nat.log 2 q) ^ 3)
    (hM : ∀ n, 2 ^ (2 ^ k) ≤ n →
      M n ≤ stepOps₂ (rootSize 1729 n) (precision n) (modelExponents 1729 n) (s n) (t n)
        (paperWindowA (precision n) (alphaParam 1729 n))
        (paperWindowE (precision n) (alphaParam 1729 n)) (paperIter (alphaParam 1729 n))
        Ecost Msmall M + C * n)
    (hbase : ∀ n, 2 ≤ n → n < 2 ^ (2 ^ k) → M n ≤ K₁ * n * (Nat.log 2 n) ^ 3) :
    ∃ D : ℝ, ∀ n, 2 ≤ n → (M n : ℝ) ≤ D * n * Real.log n := by
  have hd : 2 ≤ 1729 := by norm_num
  have hk' : 2 ^ 624 ≤ 2 ^ k := two_pow_le_two_pow hk
  have hge : 2 ^ (1729 ^ 12) ≤ 2 ^ (2 ^ k) := two_pow_le_two_pow (paper_exp_le.trans hk')
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 30 * (K₀ + K₁ + 2) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ((2880 + 4320 * K * 1729 + C : ℕ) : ℝ) / Real.log 2 :=
    ⟨_, rfl⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA0 : 0 ≤ A := by rw [hA]; exact div_nonneg (Nat.cast_nonneg _) hl2.le
  have hM0 : ∀ n, (0 : ℝ) ≤ (M n : ℝ) := fun n => Nat.cast_nonneg _
  have hparams : ∀ n, 2 ^ (2 ^ k) ≤ n →
      (transformSize n : ℝ) * precision n ≤ 48 * n ∧
        2 ≤ 3 * rootSize 1729 n * precision n ∧ 3 * rootSize 1729 n * precision n < n ∧
        0 < rootSize 1729 n ∧
        Real.log (3 * (rootSize 1729 n : ℝ) * precision n) ≤
          (1 / (1729 : ℝ) + 1 / (2 * (1729 : ℝ) ^ 2)) * Real.log n :=
    fun n hn => recurrence_params (le_trans hge hn)
  have hbase' := base_of_polylog M K₁ (2 ^ k) hbase
  have hrec : ∀ n, 2 ^ (2 ^ k) ≤ n →
      (M n : ℝ) ≤ 12 * (transformSize n : ℝ) / rootSize 1729 n *
        (M (3 * rootSize 1729 n * precision n) : ℝ) + A * n * Real.log n := by
    intro n hn
    have hn' : 2 ^ (1729 ^ 12) ≤ n := le_trans hge hn
    have hb : 2 ^ 624 ≤ chunkSize n := hk'.trans (chunkSize_ge_of_pow_le hn)
    have hp16 : 16 ≤ precision n := le_trans (by norm_num) (precision_ge hd hn')
    have hp2 : 2 ≤ precision n := le_trans (by norm_num) hp16
    have hrow := row_threshold hd hn' hb Ecost Msmall K₀ K₁ (hE _ hp16) (hM₀ _ hp2)
    rw [← hK] at hrow
    have h := le_trans (hM n hn)
      (Nat.add_le_add_right (stepOps₂_params_le hn' (s n) (t n) (ht n hn) (hst n hn) (hT n hn)
        Ecost Msmall M K hrow) _)
    have h2 := step_cost_rec_real hn' M (2880 + 4320 * K * 1729) C h
    rw [hA]
    push_cast at h2 ⊢
    exact h2
  exact main_bound (T := transformSize) (r := rootSize 1729) (p := precision)
    (n₀ := 2 ^ (2 ^ k)) (M := fun n => (M n : ℝ)) hA0 (two_le_two_pow_two_pow k) hM0
    hparams hrec hbase'

/-! ### The chosen grids and moduli -/

/-- Everything the recursive step needs about a grid and its moduli, packaged
as one existential: the grid exponents `e`, `g` and the moduli `s`, with the grid
facts of `exists_grid_lower` and the moduli facts of
`moduli_conditions_elementary`. -/
theorem exists_step_data {d' n : ℕ} (hd' : 1 ≤ d')
    (hn : 2 ^ (2 ^ (1000 * (d' + 1) ^ 3)) ≤ n) :
    ∃ (e : Fin d' → ℕ) (g : ℕ) (s : Fin (d' + 1) → ℕ),
      (∀ i, 1 ≤ e i) ∧ 1 ≤ g ∧ (∀ i, 2 ^ e i ∣ 2 * 2 ^ g) ∧
      ∏ i, lenOf e g i = transformSize n ∧ (∀ i, 0 < s i) ∧
      Pairwise (Function.onFun Nat.Coprime s) ∧ ∏ i, s i ≤ transformSize n ∧
      transformSize n < 2 * ∏ i, s i ∧ (∀ i, s i < lenOf e g i) ∧
      (∀ i, Nat.Coprime (s i) (lenOf e g i)) ∧
      ∀ i, 1 ≤ ((alphaParam (d' + 1) n : ℕ) : ℝ) ^ 2 * ((lenOf e g i : ℝ) / (s i) - 1) := by
  have hd : 2 ≤ d' + 1 := by omega
  have hn12 : 2 ^ ((d' + 1) ^ 12) ≤ n :=
    (Nat.pow_le_pow_right (by norm_num) (pow_twelve_le_two_pow (by omega))).trans hn
  obtain ⟨e, g, he, hg, hdiv, hT, hlow⟩ := exists_grid_lower (by omega) hn12
  have hk := rootExp_ge_of_big (d := d' + 1) hd hn
  have hbig : ∀ i, 2 ^ (2 ^ (500 * (d' + 1) ^ 3 + 1)) ≤ lenOf e g i := fun i =>
    (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (hlow i)
  have hpow : ∀ i, ∃ k, lenOf e g i = 2 ^ k := fun i => ⟨_, rfl⟩
  obtain ⟨s, hs0, hodd, hcop, hwin⟩ := exists_moduli_elementary hd (lenOf e g) hbig
  obtain ⟨hst, hS, hS2, hs, hcopt, hθ⟩ :=
    moduli_conditions_elementary hd hn12 (lenOf e g) s hpow hbig hs0 hodd hcop hwin
  rw [hT] at hS hS2
  exact ⟨e, g, s, he, hg, hdiv, hT, hs0, hs, hS, hS2, hst, hcopt, hθ⟩

/-- `exists_step_data` at any threshold exponent `k ≥ 1000 (d'+1)³`. -/
theorem exists_step_data' {d' k n : ℕ} (hd' : 1 ≤ d') (hk : 1000 * (d' + 1) ^ 3 ≤ k)
    (hn : 2 ^ (2 ^ k) ≤ n) :
    ∃ (e : Fin d' → ℕ) (g : ℕ) (s : Fin (d' + 1) → ℕ),
      (∀ i, 1 ≤ e i) ∧ 1 ≤ g ∧ (∀ i, 2 ^ e i ∣ 2 * 2 ^ g) ∧
      ∏ i, lenOf e g i = transformSize n ∧ (∀ i, 0 < s i) ∧
      Pairwise (Function.onFun Nat.Coprime s) ∧ ∏ i, s i ≤ transformSize n ∧
      transformSize n < 2 * ∏ i, s i ∧ (∀ i, s i < lenOf e g i) ∧
      (∀ i, Nat.Coprime (s i) (lenOf e g i)) ∧
      ∀ i, 1 ≤ ((alphaParam (d' + 1) n : ℕ) : ℝ) ^ 2 * ((lenOf e g i : ℝ) / (s i) - 1) :=
  exists_step_data hd' ((two_pow_le_two_pow (two_pow_le_two_pow hk)).trans hn)

/-- The chosen grid exponents and moduli for dimension `d' + 1` at threshold
exponent `k`: the `Classical.choose` witnesses of `exists_step_data'` above the
threshold, and the trivial data below it. -/
noncomputable def stepData (d' k n : ℕ) : (Fin d' → ℕ) × ℕ × (Fin (d' + 1) → ℕ) :=
  if h : 1 ≤ d' ∧ 1000 * (d' + 1) ^ 3 ≤ k ∧ 2 ^ (2 ^ k) ≤ n then
    ⟨Classical.choose (exists_step_data' h.1 h.2.1 h.2.2),
      Classical.choose (Classical.choose_spec (exists_step_data' h.1 h.2.1 h.2.2)),
      Classical.choose (Classical.choose_spec
        (Classical.choose_spec (exists_step_data' h.1 h.2.1 h.2.2)))⟩
  else ⟨fun _ => 1, 1, fun _ => 1⟩

/-- The chosen grid exponents. -/
noncomputable def eOf (d' k n : ℕ) : Fin d' → ℕ := (stepData d' k n).1

/-- The chosen last grid exponent. -/
noncomputable def gOf (d' k n : ℕ) : ℕ := (stepData d' k n).2.1

/-- The chosen moduli. -/
noncomputable def sOf (d' k n : ℕ) : Fin (d' + 1) → ℕ := (stepData d' k n).2.2

/-- The chosen grid lengths. -/
noncomputable def tOf (d' k n : ℕ) : Fin (d' + 1) → ℕ := lenOf (eOf d' k n) (gOf d' k n)

theorem stepData_spec {d' k n : ℕ} (hd' : 1 ≤ d') (hk : 1000 * (d' + 1) ^ 3 ≤ k)
    (hn : 2 ^ (2 ^ k) ≤ n) :
    (∀ i, 1 ≤ eOf d' k n i) ∧ 1 ≤ gOf d' k n ∧
      (∀ i, 2 ^ eOf d' k n i ∣ 2 * 2 ^ gOf d' k n) ∧
      ∏ i, tOf d' k n i = transformSize n ∧ (∀ i, 0 < sOf d' k n i) ∧
      Pairwise (Function.onFun Nat.Coprime (sOf d' k n)) ∧
      ∏ i, sOf d' k n i ≤ transformSize n ∧ transformSize n < 2 * ∏ i, sOf d' k n i ∧
      (∀ i, sOf d' k n i < tOf d' k n i) ∧
      (∀ i, Nat.Coprime (sOf d' k n i) (tOf d' k n i)) ∧
      ∀ i, 1 ≤ ((alphaParam (d' + 1) n : ℕ) : ℝ) ^ 2 *
        ((tOf d' k n i : ℝ) / (sOf d' k n i) - 1) := by
  have h : 1 ≤ d' ∧ 1000 * (d' + 1) ^ 3 ≤ k ∧ 2 ^ (2 ^ k) ≤ n := ⟨hd', hk, hn⟩
  have hspec := Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_step_data' h.1 h.2.1 h.2.2)))
  simp only [eOf, gOf, sOf, tOf, stepData, h, and_self, ↓reduceDIte]
  exact hspec

theorem stepData_of_not {d' k n : ℕ}
    (h : ¬ (1 ≤ d' ∧ 1000 * (d' + 1) ^ 3 ≤ k ∧ 2 ^ (2 ^ k) ≤ n)) :
    sOf d' k n = fun _ => 1 := by
  simp only [sOf, stepData, h, ↓reduceDIte]

instance sOf_neZero (d' k n : ℕ) (i : Fin (d' + 1)) : NeZero (sOf d' k n i) := by
  by_cases h : 1 ≤ d' ∧ 1000 * (d' + 1) ^ 3 ≤ k ∧ 2 ^ (2 ^ k) ≤ n
  · exact ⟨((stepData_spec h.1 h.2.1 h.2.2).2.2.2.2.1 i).ne'⟩
  · rw [stepData_of_not h]; exact ⟨one_ne_zero⟩

theorem sOf_pairwise (d' k n : ℕ) : Pairwise (Function.onFun Nat.Coprime (sOf d' k n)) := by
  by_cases h : 1 ≤ d' ∧ 1000 * (d' + 1) ^ 3 ≤ k ∧ 2 ^ (2 ^ k) ≤ n
  · exact (stepData_spec h.1 h.2.1 h.2.2).2.2.2.2.2.1
  · rw [stepData_of_not h]
    intro i j _
    exact Nat.coprime_one_left 1

theorem sOf_coprime (d' k n : ℕ) :
    ∀ i, Nat.Coprime (sOf d' k n i) (lenAll (Mof (eOf d' k n) (gOf d' k n)) i) := by
  rw [lenAll_Mof]
  by_cases h : 1 ≤ d' ∧ 1000 * (d' + 1) ^ 3 ≤ k ∧ 2 ^ (2 ^ k) ≤ n
  · exact (stepData_spec h.1 h.2.1 h.2.2).2.2.2.2.2.2.2.2.2.1
  · rw [stepData_of_not h]
    intro i
    exact Nat.coprime_one_left _

/-- The recursive step with the chosen grid and moduli is correct above the
threshold, for every admissible rounding oracle. -/
theorem step_correct_chosen {d' k n : ℕ} (hd' : 1 ≤ d') (hk : 1000 * (d' + 1) ^ 3 ≤ k)
    (hn : 2 ^ (2 ^ k) ≤ n) {x y : List Bool} (hx : x.length = n) (hy : y.length = n)
    (E₁ E₂ E₃ : (i : Fin d') → (m : ℕ) → Fin (2 ^ (m + 1)) →
      (Fin (lenLast (Mof (eOf d' k n) (gOf d' k n))) → ℂ))
    (hE₁ : ∀ i m j, ‖E₁ i m j‖ ≤ 1 / 2 ^ precision n)
    (hE₂ : ∀ i m j, ‖E₂ i m j‖ ≤ 1 / 2 ^ precision n)
    (hE₃ : ∀ i m j, ‖E₃ i m j‖ ≤ 1 / 2 ^ precision n) :
    recursiveStepOutputS n (eOf d' k n) (gOf d' k n) (sOf d' k n) (sOf_pairwise d' k n)
        (sOf_coprime d' k n) E₁ E₂ E₃ x y
      = Machine.binaryValue x * Machine.binaryValue y := by
  obtain ⟨he, hg, hdiv, hT, _, hs, hS, hS2, hst, hcopt, hθ⟩ := stepData_spec hd' hk hn
  have hn' : 2 ^ (2 ^ (1000 * (d' + 1) ^ 3)) ≤ n :=
    (two_pow_le_two_pow (two_pow_le_two_pow hk)).trans hn
  have hn12 : 2 ^ ((d' + 1) ^ 12) ≤ n :=
    (Nat.pow_le_pow_right (by norm_num) (pow_twelve_le_two_pow (by omega))).trans hn'
  exact recursive_step_correct_sqrt hd' hn12 hx hy (eOf d' k n) (gOf d' k n) he hg hdiv hT
    (sOf d' k n) hs hS hS2 hst hcopt hθ E₁ E₂ E₃ hE₁ hE₂ hE₃

/-! ### The capstone at `d = 1729` -/

theorem capstone_exponent_ge : 624 ≤ 1000 * (1728 + 1) ^ 3 :=
  calc 624 ≤ 1000 := by norm_num
    _ ≤ 1000 * (1728 + 1) ^ 3 := Nat.le_mul_of_pos_right _ (by positivity)

/-- Correctness of the explicit recursive step at `d = 1729` with the chosen
grids and moduli, for every `n ≥ 2^(2^(1000 · 1729³))`. -/
theorem nlogn_capstone_correct {n : ℕ} (hn : 2 ^ (2 ^ (1000 * (1728 + 1) ^ 3)) ≤ n)
    {x y : List Bool} (hx : x.length = n) (hy : y.length = n)
    (E₁ E₂ E₃ : (i : Fin 1728) → (m : ℕ) → Fin (2 ^ (m + 1)) →
      (Fin (lenLast (Mof (eOf 1728 (1000 * (1728 + 1) ^ 3) n)
        (gOf 1728 (1000 * (1728 + 1) ^ 3) n))) → ℂ))
    (hE₁ : ∀ i m j, ‖E₁ i m j‖ ≤ 1 / 2 ^ precision n)
    (hE₂ : ∀ i m j, ‖E₂ i m j‖ ≤ 1 / 2 ^ precision n)
    (hE₃ : ∀ i m j, ‖E₃ i m j‖ ≤ 1 / 2 ^ precision n) :
    recursiveStepOutputS n (eOf 1728 (1000 * (1728 + 1) ^ 3) n)
        (gOf 1728 (1000 * (1728 + 1) ^ 3) n) (sOf 1728 (1000 * (1728 + 1) ^ 3) n)
        (sOf_pairwise _ _ _) (sOf_coprime _ _ _) E₁ E₂ E₃ x y
      = Machine.binaryValue x * Machine.binaryValue y :=
  step_correct_chosen (Nat.one_le_iff_ne_zero.mpr (by decide)) le_rfl hn hx hy E₁ E₂ E₃
    hE₁ hE₂ hE₃

/-- The cost of the explicit recursive step at `d = 1729` with the chosen grids
and moduli: any cost bounded above the threshold by one full step plus a linear
overhead, and below it by the plain multiplier's bound, is `O(n log n)`. -/
theorem nlogn_capstone_cost (M : ℕ → ℕ) (C : ℕ)
    (hM : ∀ n, 2 ^ (2 ^ (1000 * (1728 + 1) ^ 3)) ≤ n →
      M n ≤ stepOps₂ (rootSize 1729 n) (precision n) (modelExponents 1729 n)
        (sOf 1728 (1000 * (1728 + 1) ^ 3) n) (tOf 1728 (1000 * (1728 + 1) ^ 3) n)
        (paperWindowA (precision n) (alphaParam 1729 n))
        (paperWindowE (precision n) (alphaParam 1729 n)) (paperIter (alphaParam 1729 n))
        expCost Mcost₀ M + C * n)
    (hbase : ∀ n, 2 ≤ n → n < 2 ^ (2 ^ (1000 * (1728 + 1) ^ 3)) →
      M n ≤ 4 * 10 ^ 6 * n * (Nat.log 2 n) ^ 3) :
    ∃ D : ℝ, ∀ n, 2 ≤ n → (M n : ℝ) ≤ D * n * Real.log n := by
  have hd' : 1 ≤ 1728 := Nat.one_le_iff_ne_zero.mpr (by decide)
  refine joint_cost_nlogn_at (1000 * (1728 + 1) ^ 3) capstone_exponent_ge M Mcost₀ expCost
    (16 * 10 ^ 11) (4 * 10 ^ 6) C (fun n => sOf 1728 (1000 * (1728 + 1) ^ 3) n)
    (fun n => tOf 1728 (1000 * (1728 + 1) ^ 3) n) ?_ ?_ ?_
    (fun _ hq => expCost_le_log4 hq) (fun _ hq => Mcost₀_le_cube hq) hM hbase
  · intro n _ i
    exact pow_pos (by norm_num) _
  · intro n hn i
    exact ((stepData_spec hd' le_rfl hn).2.2.2.2.2.2.2.2.1 i).le
  · intro n hn
    exact (stepData_spec hd' le_rfl hn).2.2.2.1

/-- The capstone: correctness and cost together. -/
theorem nlogn_capstone :
    (∀ n, 2 ^ (2 ^ (1000 * (1728 + 1) ^ 3)) ≤ n → ∀ x y : List Bool, x.length = n →
      y.length = n →
      ∀ (E₁ E₂ E₃ : (i : Fin 1728) → (m : ℕ) → Fin (2 ^ (m + 1)) →
        (Fin (lenLast (Mof (eOf 1728 (1000 * (1728 + 1) ^ 3) n)
          (gOf 1728 (1000 * (1728 + 1) ^ 3) n))) → ℂ)),
        (∀ i m j, ‖E₁ i m j‖ ≤ 1 / 2 ^ precision n) →
        (∀ i m j, ‖E₂ i m j‖ ≤ 1 / 2 ^ precision n) →
        (∀ i m j, ‖E₃ i m j‖ ≤ 1 / 2 ^ precision n) →
        recursiveStepOutputS n (eOf 1728 (1000 * (1728 + 1) ^ 3) n)
            (gOf 1728 (1000 * (1728 + 1) ^ 3) n) (sOf 1728 (1000 * (1728 + 1) ^ 3) n)
            (sOf_pairwise _ _ _) (sOf_coprime _ _ _) E₁ E₂ E₃ x y
          = Machine.binaryValue x * Machine.binaryValue y) ∧
    (∀ (M : ℕ → ℕ) (C : ℕ),
      (∀ n, 2 ^ (2 ^ (1000 * (1728 + 1) ^ 3)) ≤ n →
        M n ≤ stepOps₂ (rootSize 1729 n) (precision n) (modelExponents 1729 n)
          (sOf 1728 (1000 * (1728 + 1) ^ 3) n) (tOf 1728 (1000 * (1728 + 1) ^ 3) n)
          (paperWindowA (precision n) (alphaParam 1729 n))
          (paperWindowE (precision n) (alphaParam 1729 n)) (paperIter (alphaParam 1729 n))
          expCost Mcost₀ M + C * n) →
      (∀ n, 2 ≤ n → n < 2 ^ (2 ^ (1000 * (1728 + 1) ^ 3)) →
        M n ≤ 4 * 10 ^ 6 * n * (Nat.log 2 n) ^ 3) →
      ∃ D : ℝ, ∀ n, 2 ≤ n → (M n : ℝ) ≤ D * n * Real.log n) :=
  ⟨fun _ hn _ _ hx hy E₁ E₂ E₃ hE₁ hE₂ hE₃ =>
      nlogn_capstone_correct hn hx hy E₁ E₂ E₃ hE₁ hE₂ hE₃,
    fun M C hM hbase => nlogn_capstone_cost M C hM hbase⟩

end IntegerMultBounds.NLogN
