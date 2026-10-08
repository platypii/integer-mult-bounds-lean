import IntegerMultBounds.NLogN.ModuliConstruction
import IntegerMultBounds.NLogN.ContractSqrt

/-! The final recursive-step theorem of the `O(n log n)` subroutine, with the
paper's window sizes. For every dimension `d = d' + 1 ≥ 2` and every
`n ≥ 2^(2^(1000 d³))`, there are a power-of-two grid, odd pairwise coprime
moduli below the grid lengths, and the explicit numerical recursive step
(resampling tensors with windows `(⌊√p⌋ + 1) α` and `⌊√p⌋ + 1`, the clamped
Bluestein power-of-two transform, rounded pointwise products, scaling, and
rounding) returns exactly the product of any two `n`-bit inputs whenever the
per-level rounding oracles are within `2^(−p)`.

Nothing beyond that threshold and the oracle bounds is assumed: the moduli are
constructed elementarily, so no Chebyshev-function bound is used. Operation
counts for the same maps live in the cost files; tape steps are not modelled
here. -/

namespace IntegerMultBounds.NLogN

/-- The unconditional recursive step with the paper's windows: the hypotheses of
`nlogn_step_unconditional`, the output of `ContractSqrt`. -/
theorem nlogn_step_unconditional_sqrt {d' n : ℕ} (hd' : 1 ≤ d')
    (hn : 2 ^ (2 ^ (1000 * (d' + 1) ^ 3)) ≤ n) {x y : List Bool}
    (hx : x.length = n) (hy : y.length = n) :
    ∃ (e : Fin d' → ℕ) (g : ℕ) (s : Fin (d' + 1) → ℕ) (_ : ∀ i, NeZero (s i))
      (hs : Pairwise (Function.onFun Nat.Coprime s))
      (hcop : ∀ i, Nat.Coprime (s i) (lenAll (Mof e g) i)),
      (∀ i, ¬ 2 ∣ s i) ∧ (∀ i, s i < lenOf e g i) ∧
      ∀ (E₁ E₂ E₃ : (i : Fin d') → (m : ℕ) → Fin (2 ^ (m + 1)) →
          (Fin (lenLast (Mof e g)) → ℂ)),
        (∀ i m k, ‖E₁ i m k‖ ≤ 1 / 2 ^ precision n) →
        (∀ i m k, ‖E₂ i m k‖ ≤ 1 / 2 ^ precision n) →
        (∀ i m k, ‖E₃ i m k‖ ≤ 1 / 2 ^ precision n) →
        recursiveStepOutputS n e g s hs hcop E₁ E₂ E₃ x y
          = Machine.binaryValue x * Machine.binaryValue y := by
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
  have : ∀ i, NeZero (s i) := fun i => ⟨(hs0 i).ne'⟩
  rw [hT] at hS hS2
  refine ⟨e, g, s, inferInstance, hs, by rw [lenAll_Mof]; exact hcopt, hodd, hst, ?_⟩
  intro E₁ E₂ E₃ hE₁ hE₂ hE₃
  exact recursive_step_correct_sqrt (by omega) hn12 hx hy e g he hg hdiv hT s hs hS hS2
    hst hcopt hθ E₁ E₂ E₃ hE₁ hE₂ hE₃

/-- The paper's dimension `d = 1729` (written `1728 + 1` so that the statement is
syntactically the instance `d' = 1728` of the general theorem and no large
numeral is ever evaluated): the unconditional recursive step with the paper's
windows for every `n ≥ 2^(2^(1000 · 1729³))`. -/
theorem nlogn_step_1729 {n : ℕ} (hn : 2 ^ (2 ^ (1000 * (1728 + 1) ^ 3)) ≤ n)
    {x y : List Bool} (hx : x.length = n) (hy : y.length = n) :
    ∃ (e : Fin 1728 → ℕ) (g : ℕ) (s : Fin (1728 + 1) → ℕ) (_ : ∀ i, NeZero (s i))
      (hs : Pairwise (Function.onFun Nat.Coprime s))
      (hcop : ∀ i, Nat.Coprime (s i) (lenAll (Mof e g) i)),
      (∀ i, ¬ 2 ∣ s i) ∧ (∀ i, s i < lenOf e g i) ∧
      ∀ (E₁ E₂ E₃ : (i : Fin 1728) → (m : ℕ) → Fin (2 ^ (m + 1)) →
          (Fin (lenLast (Mof e g)) → ℂ)),
        (∀ i m k, ‖E₁ i m k‖ ≤ 1 / 2 ^ precision n) →
        (∀ i m k, ‖E₂ i m k‖ ≤ 1 / 2 ^ precision n) →
        (∀ i m k, ‖E₃ i m k‖ ≤ 1 / 2 ^ precision n) →
        recursiveStepOutputS n e g s hs hcop E₁ E₂ E₃ x y
          = Machine.binaryValue x * Machine.binaryValue y :=
  nlogn_step_unconditional_sqrt (d' := 1728) (Nat.one_le_iff_ne_zero.mpr (by decide)) hn hx hy

end IntegerMultBounds.NLogN
