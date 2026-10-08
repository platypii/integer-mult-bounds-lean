import IntegerMultBounds.NLogN.ContractPrep
import IntegerMultBounds.NLogN.PowerOfTwoContract

/-! The correctness contract of the `O(n log n)` recursive step in the vector
model. For `d = d' + 1 ≥ 2`, `n ≥ 2^(d^12)`, and `n`-bit inputs, the
power-of-two grid of the paper's Section 5.1 exists with lengths
`2^(e_i)` and last length `2^g`; and for any choice of pairwise coprime
moduli `s_i < t_i` coprime to `t_i` with `α²(t_i/s_i − 1) ≥ 1` and
`∏ s_i ≤ T < 2 ∏ s_i`, the fully explicit numerical algorithm (the clamped
resampling tensors of `ExplicitNumeric.lean`, the clamped power-of-two
transform of `PowerOfTwoContract.lean`, rounded pointwise products, and the
final scaling and rounding) returns the exact product of the inputs, for every
admissible choice of the per-level rounding oracles.

The one remaining mathematical hypothesis is the existence of such moduli
`s_i`: the paper's Lemma 5.1 takes primes in short intervals below each `t_i`
and needs explicit Chebyshev bounds that mathlib does not have. Bit costs of
the step (beyond the operation counts of `CostModel.lean`) and the compilation
to tape machines are separate obligations. -/

namespace IntegerMultBounds.NLogN

open scoped BigOperators

section Output

variable {d' n : ℕ}

/-- The output of the explicit recursive step: the rounded, rescaled approximate
scaled convolution of the digit vectors on the Chinese-remainder grid, read as a
base-`2^b` number. -/
noncomputable def recursiveStepOutput (n : ℕ) (e : Fin d' → ℕ) (g : ℕ)
    (s : Fin (d' + 1) → ℕ) [∀ i, NeZero (s i)] (hs : Pairwise (Function.onFun Nat.Coprime s))
    (hcop : ∀ i, Nat.Coprime (s i) (lenAll (Mof e g) i))
    (E₁ E₂ E₃ : (i : Fin d') → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin (lenLast (Mof e g)) → ℂ))
    (x y : List Bool) : ℕ :=
  let F' := mainTransformNum (gammaParam (d' + 1) n + 2 * (d' + 1))
    (resampANumX (precision n) s (lenAll (Mof e g)) (alphaParam (d' + 1) n : ℝ))
    (resampBNumX (precision n) s (lenAll (Mof e g)) (alphaParam (d' + 1) n : ℝ) hcop)
    (powerOfTwoNum e g (precision n) E₁ E₂ E₃)
  evalBase (2 ^ chunkSize n) (List.ofFn fun i : Fin (∏ i, s i) =>
    (round (((2 : ℂ) ^ (2 * chunkSize n) * (∏ i, s i : ℕ)) *
      approxConvS hs (precision n) (chunkSize n) F' (fun v => negVec (F' v))
        (digitsOf (chunkSize n) x) (digitsOf (chunkSize n) y)
        (i.val : ZMod (∏ i, s i))).re).toNat)

theorem one_le_sum_of_forall {e : Fin d' → ℕ} (hd' : 1 ≤ d') (he : ∀ i, 1 ≤ e i) :
    1 ≤ ∑ i, e i := by
  have h0 : 0 < d' := hd'
  calc 1 ≤ e ⟨0, h0⟩ := he _
    _ ≤ ∑ i, e i := Finset.single_le_sum (fun i _ => Nat.zero_le (e i)) (Finset.mem_univ _)

/-- The recursive step is correct for every admissible modulus choice and every
admissible rounding oracle. -/
theorem recursive_step_correct (hd' : 1 ≤ d') (hn : 2 ^ ((d' + 1) ^ 12) ≤ n) {x y : List Bool}
    (hx : x.length = n) (hy : y.length = n) (e : Fin d' → ℕ) (g : ℕ)
    (he : ∀ i, 1 ≤ e i) (hg : 1 ≤ g) (hdiv : ∀ i, 2 ^ e i ∣ 2 * 2 ^ g)
    (hT : ∏ i, lenOf e g i = transformSize n)
    (s : Fin (d' + 1) → ℕ) [∀ i, NeZero (s i)] (hs : Pairwise (Function.onFun Nat.Coprime s))
    (hS : ∏ i, s i ≤ transformSize n) (hS2 : transformSize n < 2 * ∏ i, s i)
    (hst : ∀ i, s i < lenOf e g i) (hcop : ∀ i, Nat.Coprime (s i) (lenOf e g i))
    (hθ : ∀ i, 1 ≤ ((alphaParam (d' + 1) n : ℕ) : ℝ) ^ 2 * ((lenOf e g i : ℝ) / (s i) - 1))
    (E₁ E₂ E₃ : (i : Fin d') → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin (lenLast (Mof e g)) → ℂ))
    (hE₁ : ∀ i m k, ‖E₁ i m k‖ ≤ 1 / 2 ^ precision n)
    (hE₂ : ∀ i m k, ‖E₂ i m k‖ ≤ 1 / 2 ^ precision n)
    (hE₃ : ∀ i m k, ‖E₃ i m k‖ ≤ 1 / 2 ^ precision n) :
    recursiveStepOutput n e g s hs (by rw [lenAll_Mof]; exact hcop) E₁ E₂ E₃ x y
      = Machine.binaryValue x * Machine.binaryValue y := by
  have hL := lenAll_Mof e g
  rw [← hL] at hst hθ hT
  have hcop' : ∀ i, Nat.Coprime (s i) (lenAll (Mof e g) i) := by rw [hL]; exact hcop
  have hsum : 1 ≤ ∑ i, e i := one_le_sum_of_forall hd' he
  have hbound := powerOfTwo_contract_bound e g hg hsum
  rw [← hL, hT] at hbound
  unfold recursiveStepOutput
  exact main_step_explicit (s := s) (t := lenAll (Mof e g)) (by omega) hn hx hy hs hS hS2 hst
    hcop' hθ (powerOfTwoNum e g (precision n) E₁ E₂ E₃)
    (approxMap_powerOfTwoNum e g he hg hdiv hE₁ hE₂ hE₃)
    (fun u _ => powerOfTwoNum_ball e g (precision n) E₁ E₂ E₃ u) hbound

end Output

section Grid

variable {d' n : ℕ}

theorem one_le_of_two_le_two_pow {k : ℕ} (h : 2 ≤ 2 ^ k) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; norm_num at h
  · exact hk

/-- The power-of-two grid of Section 5.1 in exponent form: `t_i = 2^(e_i)` for
`i < d'`, `t_{d'} = 2^g = r`, all lengths at least two, each dividing `2r`, with
product `T` and each at most `r`. -/
theorem exists_grid (hd' : 1 ≤ d') (hn : 2 ^ ((d' + 1) ^ 12) ≤ n) :
    ∃ (e : Fin d' → ℕ) (g : ℕ), (∀ i, 1 ≤ e i) ∧ 1 ≤ g ∧ (∀ i, 2 ^ e i ∣ 2 * 2 ^ g) ∧
      ∏ i, lenOf e g i = transformSize n ∧ ∀ i, lenOf e g i ≤ rootSize (d' + 1) n := by
  obtain ⟨t, ht1, ht2, hmono, hprod, hle⟩ := exists_factorisation (d := d' + 1) (by omega) hn
  choose f hf using ht1
  refine ⟨fun i => f (Fin.castSucc i), f (Fin.last d'), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have := ht2 (Fin.castSucc i)
    rw [hf] at this
    exact one_le_of_two_le_two_pow this
  · have := ht2 (Fin.last d')
    rw [hf] at this
    exact one_le_of_two_le_two_pow this
  · intro i
    have hle' : t (Fin.castSucc i) ≤ t (Fin.last d') := hmono (Fin.castSucc_lt_last i).le
    rw [hf, hf] at hle'
    have hexp : f (Fin.castSucc i) ≤ f (Fin.last d') :=
      (Nat.pow_le_pow_iff_right (by norm_num)).mp hle'
    exact (pow_dvd_pow 2 hexp).trans (Dvd.intro_left 2 rfl)
  · have heq : lenOf (fun i => f (Fin.castSucc i)) (f (Fin.last d')) = t := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [lenOf, Fin.snoc_last]; exact (hf _).symm
      · simp only [lenOf, Fin.snoc_castSucc]; exact (hf _).symm
    rw [heq]; exact hprod
  · intro i
    have heq : lenOf (fun i => f (Fin.castSucc i)) (f (Fin.last d')) i = t i := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [lenOf, Fin.snoc_last]; exact (hf _).symm
      · simp only [lenOf, Fin.snoc_castSucc]; exact (hf _).symm
    rw [heq]; exact hle i

end Grid

section Headline

variable {d' n : ℕ}

/-- The headline contract of the recursive step. For `d = d' + 1 ≥ 2` and
`n ≥ 2^(d^12)` there is a power-of-two grid such that, for every choice of
pairwise coprime moduli `s_i < t_i` coprime to `t_i` with the decay condition
`α²(t_i/s_i − 1) ≥ 1` and `∏ s_i ≤ T < 2 ∏ s_i`, and every admissible rounding
oracle, the explicit numerical step returns the exact product of any two
`n`-bit inputs. The existence of such moduli is the paper's Lemma 5.1 and is
not proved here. -/
theorem nlogn_step_contract (hd' : 1 ≤ d') (hn : 2 ^ ((d' + 1) ^ 12) ≤ n) {x y : List Bool}
    (hx : x.length = n) (hy : y.length = n) :
    ∃ (e : Fin d' → ℕ) (g : ℕ), (∀ i, 1 ≤ e i) ∧ 1 ≤ g ∧
      ∏ i, lenOf e g i = transformSize n ∧ (∀ i, lenOf e g i ≤ rootSize (d' + 1) n) ∧
      ∀ (s : Fin (d' + 1) → ℕ) [∀ i, NeZero (s i)]
        (hs : Pairwise (Function.onFun Nat.Coprime s)),
        ∏ i, s i ≤ transformSize n → transformSize n < 2 * ∏ i, s i →
        (∀ i, s i < lenOf e g i) →
        ∀ hcop : ∀ i, Nat.Coprime (s i) (lenOf e g i),
        (∀ i, 1 ≤ ((alphaParam (d' + 1) n : ℕ) : ℝ) ^ 2 * ((lenOf e g i : ℝ) / (s i) - 1)) →
        ∀ (E₁ E₂ E₃ : (i : Fin d') → (m : ℕ) → Fin (2 ^ (m + 1)) →
            (Fin (lenLast (Mof e g)) → ℂ)),
          (∀ i m k, ‖E₁ i m k‖ ≤ 1 / 2 ^ precision n) →
          (∀ i m k, ‖E₂ i m k‖ ≤ 1 / 2 ^ precision n) →
          (∀ i m k, ‖E₃ i m k‖ ≤ 1 / 2 ^ precision n) →
          recursiveStepOutput n e g s hs (by rw [lenAll_Mof]; exact hcop) E₁ E₂ E₃ x y
            = Machine.binaryValue x * Machine.binaryValue y := by
  obtain ⟨e, g, he, hg, hdiv, hT, hle⟩ := exists_grid hd' hn
  refine ⟨e, g, he, hg, hT, hle, ?_⟩
  intro s _ hs hS hS2 hst hcop hθ E₁ E₂ E₃ hE₁ hE₂ hE₃
  exact recursive_step_correct hd' hn hx hy e g he hg hdiv hT s hs hS hS2 hst hcop hθ
    E₁ E₂ E₃ hE₁ hE₂ hE₃

end Headline

end IntegerMultBounds.NLogN
