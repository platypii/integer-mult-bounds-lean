import IntegerMultBounds.NLogN.Contract
import IntegerMultBounds.NLogN.OffDiagApproxSqrt

/-! The recursive-step contract with the paper's window sizes. `Contract.lean`
instantiates both truncation windows at `m = p`, which is simplest for the
error analysis but too wide for the cost model. Here the resampling map `Ã_i`
uses the window `(⌊√p⌋ + 1) α` of Lemma 4.9 and the off-diagonal part inside
`B̃_i` uses the window `⌊√p⌋ + 1` of Lemma 4.11 (`OffDiagApproxSqrt.lean`);
everything else is unchanged. The window for `Ã` is at most `2p`, so its error
`(8 m + 7)/2` is still below `p²`, and the headline contract
`nlogn_step_contract_sqrt` has exactly the hypotheses of `nlogn_step_contract`.
Operation counts are not in this file. -/

namespace IntegerMultBounds.NLogN

open scoped BigOperators

section Windows

variable {d n : ℕ}

/-- The window of Lemma 4.9 for `Ã`: `(⌊√p⌋ + 1) α`. -/
noncomputable def mA (d n : ℕ) : ℕ := sqrtWindow (precision n) * alphaParam d n

/-- The window of Lemma 4.11 for the off-diagonal part of `B̃`: `⌊√p⌋ + 1`. -/
def mE (n : ℕ) : ℕ := sqrtWindow (precision n)

theorem one_le_mA (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) : 1 ≤ mA d n := by
  have hb := chunkSize_ge_4096 hd hn
  have hα := alphaParam_ge_two (d := d) (n := n) (by omega) (by omega)
  have hw := one_le_sqrtWindow (precision n)
  unfold mA
  nlinarith

/-- `p α² ≤ mA²`, since `p < (⌊√p⌋ + 1)²`. -/
theorem mA_sq (d n : ℕ) :
    (precision n : ℝ) * ((alphaParam d n : ℕ) : ℝ) ^ 2 ≤ ((mA d n : ℕ) : ℝ) ^ 2 := by
  have h : precision n * alphaParam d n ^ 2 ≤ mA d n ^ 2 := by
    have hp : precision n ≤ sqrtWindow (precision n) ^ 2 := by
      have := Nat.lt_succ_sqrt (precision n)
      unfold sqrtWindow
      nlinarith
    unfold mA
    rw [mul_pow]
    exact Nat.mul_le_mul_right _ hp
  exact_mod_cast h

/-- The window for `Ã` is at most `2p`, from `α² < p`. -/
theorem mA_le_two_p (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) : mA d n ≤ 2 * precision n := by
  have hα2 := alphaParam_sq_lt_precision hd hn
  have hα : alphaParam d n ≤ Nat.sqrt (precision n) := by
    rw [Nat.le_sqrt]
    nlinarith
  have hs := Nat.sqrt_le_self (precision n)
  have hsq : Nat.sqrt (precision n) * Nat.sqrt (precision n) ≤ precision n :=
    Nat.sqrt_le (precision n)
  unfold mA sqrtWindow
  nlinarith

/-- With the window at most `2p`, the explicit `ε(Ã) = (8m + 7)/2` is below `p²`
for `p ≥ 9`. -/
theorem errA_sqrt_lt_sq {p m : ℕ} (hmA : m ≤ 2 * p) (hp : 9 ≤ p) :
    (4 * (2 * (m : ℝ) + 1) + 3) / 2 < (p : ℝ) ^ 2 := by
  have h1 : (m : ℝ) ≤ 2 * p := by exact_mod_cast hmA
  have h2 : (9 : ℝ) ≤ p := by exact_mod_cast hp
  nlinarith

end Windows

section Explicit

variable {d n : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]

/-- The explicit numerical `Ã_i` at the window `(⌊√p⌋ + 1) α`, clamped. -/
noncomputable def resampANumS (d n : ℕ) (s t : Fin d → ℕ) [∀ i, NeZero (s i)]
    [∀ i, NeZero (t i)] (i : Fin d) : (ZMod (s i) → ℂ) → (ZMod (t i) → ℂ) :=
  clampV ∘ resampANum (s i) (t i) (mA d n)
    (resampTermNum (precision n) (s i) (t i) (alphaParam d n : ℝ))

/-- The explicit numerical `B̃_i` with the off-diagonal window `⌊√p⌋ + 1`, clamped. -/
noncomputable def resampBNumS (d n : ℕ) (s t : Fin d → ℕ) [∀ i, NeZero (s i)]
    [∀ i, NeZero (t i)] (hcop : ∀ i, Nat.Coprime (s i) (t i)) (i : Fin d) :
    (ZMod (t i) → ℂ) → (ZMod (s i) → ℂ) :=
  clampV ∘ resampBNumC (precision n) (mE n) (s i) (t i) (alphaParam d n : ℝ) (hcop i)

theorem resampANumS_ball (i : Fin d) (v : ZMod (s i) → ℂ) : ‖resampANumS d n s t i v‖ ≤ 1 :=
  clamp_ball _ v

theorem resampBNumS_ball (hcop : ∀ i, Nat.Coprime (s i) (t i)) (i : Fin d)
    (v : ZMod (t i) → ℂ) : ‖resampBNumS d n s t hcop i v‖ ≤ 1 :=
  clamp_ball _ v

/-- Lemma 4.9 at the paper's window: `ε(Ã_i) ≤ (8 mA + 7)/2`. -/
theorem approxMap_resampANumS (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) (i : Fin d) :
    ApproxMap (precision n) (resampANumS d n s t i)
      (resampA (s i) (t i) (alphaParam d n : ℝ)) ((4 * (2 * (mA d n : ℕ) + 1) + 3) / 2) := by
  obtain ⟨hα, hαp, _, _⟩ := params_ok hd hn
  exact approxMap_clamp (opNorm_resampA_le hα)
    (approxMap_resampANum_explicit hα hαp (mA_sq d n) (one_le_mA hd hn))

/-- Lemma 4.11 at the paper's window: `ε(B̃_i) ≤ (24 mE + 23)/2`. -/
theorem approxMap_resampBNumS (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) (hst : ∀ i, s i < t i)
    (hcop : ∀ i, Nat.Coprime (s i) (t i))
    (hθ : ∀ i, 1 ≤ ((alphaParam d n : ℕ) : ℝ) ^ 2 * ((t i : ℝ) / (s i) - 1))
    (J : (i : Fin d) → (ZMod (s i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ))
    (hJ : ∀ i, J i ∘L (1 + offDiagCLM (s i) (t i) (alphaParam d n : ℝ)) = 1)
    (hJ' : ∀ i, (1 + offDiagCLM (s i) (t i) (alphaParam d n : ℝ)) ∘L J i = 1) (i : Fin d) :
    ApproxMap (precision n) (resampBNumS d n s t hcop i)
      (resampB (s i) (t i) (alphaParam d n : ℝ) (hcop i) (J i))
      ((6 + (2 * ((6 * (2 * (mE n : ℕ)) + 6) + 2) + 1)) / 2) := by
  obtain ⟨hα, _, _, _⟩ := params_ok hd hn
  exact approxMap_clamp
    (resampling_factorization_explicit (hst i) (hcop i) hα (hθ i) (J i) (hJ i)).2.2
    (approxMap_resampBNumC_sqrt (hst i) (hcop i) (by linarith) (hθ i)
      (sqrtWindow_bound (precision n)) (hJ' i))

end Explicit

section Step

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]

/-- `main_step_explicit` with the paper's windows. -/
theorem main_step_explicit_sqrt {n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) {x y : List Bool}
    (hx : x.length = n) (hy : y.length = n) (hs : Pairwise (Function.onFun Nat.Coprime s))
    (hS : ∏ i, s i ≤ transformSize n) (hS2 : transformSize n < 2 * ∏ i, s i)
    (hst : ∀ i, s i < t i) (hcop : ∀ i, Nat.Coprime (s i) (t i))
    (hθ : ∀ i, 1 ≤ ((alphaParam d n : ℕ) : ℝ) ^ 2 * ((t i : ℝ) / (s i) - 1))
    (Ft' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ)) {εFt : ℝ}
    (hFt : ApproxMap (precision n) Ft' (dftDCLM t) εFt)
    (hFt'ball : ∀ u, ‖u‖ ≤ 1 → ‖Ft' u‖ ≤ 1)
    (hεFt : εFt ≤ 8 * (transformSize n : ℝ) * (Nat.log 2 (transformSize n) : ℝ)) :
    evalBase (2 ^ chunkSize n) (List.ofFn fun i : Fin (∏ i, s i) =>
      (round (((2 : ℂ) ^ (2 * chunkSize n) * (∏ i, s i : ℕ)) *
        approxConvS hs (precision n) (chunkSize n)
          (mainTransformNum (gammaParam d n + 2 * d)
            (resampANumS d n s t) (resampBNumS d n s t hcop) Ft')
          (fun v => negVec (mainTransformNum (gammaParam d n + 2 * d)
            (resampANumS d n s t) (resampBNumS d n s t hcop) Ft' v))
          (digitsOf (chunkSize n) x) (digitsOf (chunkSize n) y)
          (i.val : ZMod (∏ i, s i))).re).toNat)
      = Machine.binaryValue x * Machine.binaryValue y := by
  obtain ⟨hα, _, _, hp13⟩ := params_ok hd hn
  have hα0 : (0 : ℝ) < ((alphaParam d n : ℕ) : ℝ) := by linarith
  have hex : ∀ i, ∃ J : (ZMod (s i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ),
      J ∘L (1 + offDiagCLM (s i) (t i) (alphaParam d n : ℝ)) = 1 ∧
        (1 + offDiagCLM (s i) (t i) (alphaParam d n : ℝ)) ∘L J = 1 ∧ ‖J‖ ≤ 2 :=
    fun i => exists_left_inverse (hst i) hα0 (hθ i)
  choose J hJ hJ' _ using hex
  have hεA := (errA_sqrt_lt_sq (p := precision n) (mA_le_two_p hd hn) (by omega)).le
  have hεB := (errB_sqrt_lt_sq (p := precision n) hp13).le
  exact main_step_full hd hn hx hy hs hS hS2 hst hcop hθ J hJ
    (resampANumS d n s t) (resampBNumS d n s t hcop)
    (approxMap_resampANumS hd hn) (approxMap_resampBNumS hd hn hst hcop hθ J hJ hJ')
    (fun i v _ => resampANumS_ball i v) (fun i v _ => resampBNumS_ball hcop i v)
    Ft' hFt hFt'ball hεA hεB hεFt

end Step

section Output

variable {d' n : ℕ}

/-- The output of the explicit recursive step with the paper's windows. -/
noncomputable def recursiveStepOutputS (n : ℕ) (e : Fin d' → ℕ) (g : ℕ)
    (s : Fin (d' + 1) → ℕ) [∀ i, NeZero (s i)] (hs : Pairwise (Function.onFun Nat.Coprime s))
    (hcop : ∀ i, Nat.Coprime (s i) (lenAll (Mof e g) i))
    (E₁ E₂ E₃ : (i : Fin d') → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin (lenLast (Mof e g)) → ℂ))
    (x y : List Bool) : ℕ :=
  let F' := mainTransformNum (gammaParam (d' + 1) n + 2 * (d' + 1))
    (resampANumS (d' + 1) n s (lenAll (Mof e g)))
    (resampBNumS (d' + 1) n s (lenAll (Mof e g)) hcop)
    (powerOfTwoNum e g (precision n) E₁ E₂ E₃)
  evalBase (2 ^ chunkSize n) (List.ofFn fun i : Fin (∏ i, s i) =>
    (round (((2 : ℂ) ^ (2 * chunkSize n) * (∏ i, s i : ℕ)) *
      approxConvS hs (precision n) (chunkSize n) F' (fun v => negVec (F' v))
        (digitsOf (chunkSize n) x) (digitsOf (chunkSize n) y)
        (i.val : ZMod (∏ i, s i))).re).toNat)

/-- The recursive step with the paper's windows is correct for every admissible
modulus choice and every admissible rounding oracle. -/
theorem recursive_step_correct_sqrt (hd' : 1 ≤ d') (hn : 2 ^ ((d' + 1) ^ 12) ≤ n)
    {x y : List Bool} (hx : x.length = n) (hy : y.length = n) (e : Fin d' → ℕ) (g : ℕ)
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
    recursiveStepOutputS n e g s hs (by rw [lenAll_Mof]; exact hcop) E₁ E₂ E₃ x y
      = Machine.binaryValue x * Machine.binaryValue y := by
  have hL := lenAll_Mof e g
  rw [← hL] at hst hθ hT
  have hcop' : ∀ i, Nat.Coprime (s i) (lenAll (Mof e g) i) := by rw [hL]; exact hcop
  have hsum : 1 ≤ ∑ i, e i := one_le_sum_of_forall hd' he
  have hbound := powerOfTwo_contract_bound e g hg hsum
  rw [← hL, hT] at hbound
  unfold recursiveStepOutputS
  exact main_step_explicit_sqrt (s := s) (t := lenAll (Mof e g)) (by omega) hn hx hy hs hS hS2
    hst hcop' hθ (powerOfTwoNum e g (precision n) E₁ E₂ E₃)
    (approxMap_powerOfTwoNum e g he hg hdiv hE₁ hE₂ hE₃)
    (fun u _ => powerOfTwoNum_ball e g (precision n) E₁ E₂ E₃ u) hbound

/-- The headline contract with the paper's windows; the hypotheses are those of
`nlogn_step_contract`. -/
theorem nlogn_step_contract_sqrt (hd' : 1 ≤ d') (hn : 2 ^ ((d' + 1) ^ 12) ≤ n)
    {x y : List Bool} (hx : x.length = n) (hy : y.length = n) :
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
          recursiveStepOutputS n e g s hs (by rw [lenAll_Mof]; exact hcop) E₁ E₂ E₃ x y
            = Machine.binaryValue x * Machine.binaryValue y := by
  obtain ⟨e, g, he, hg, hdiv, hT, hle⟩ := exists_grid hd' hn
  refine ⟨e, g, he, hg, hT, hle, ?_⟩
  intro s _ hs hS hS2 hst hcop hθ E₁ E₂ E₃ hE₁ hE₂ hE₃
  exact recursive_step_correct_sqrt hd' hn hx hy e g he hg hdiv hT s hs hS hS2 hst hcop hθ
    E₁ E₂ E₃ hE₁ hE₂ hE₃

end Output

end IntegerMultBounds.NLogN
