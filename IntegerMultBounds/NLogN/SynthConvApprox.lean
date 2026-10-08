import IntegerMultBounds.NLogN.SynthConv
import IntegerMultBounds.NLogN.Section5Approx

/-! Proposition 3.4 of Harvey and van der Hoeven in one dimension over the
synthetic ring in coefficient form. The normalised convolution
`M_R(u, v) = (1/t) u ∗ v` of vectors of length `t = 2^n ∣ 2r` equals
`t r` times the inverse synthetic transform of the pointwise negacyclic
products of the forward transforms, each product scaled by `1/r`. Evaluating
this pipeline with per-level error oracles of size `2^(-p)` in all three
transforms and componentwise rounding of the products gives an absolute error
of at most `(3n + 2)/2^p + (n/2^p)^2` before the final scaling, hence scaled
error at most `4n + 2` once `n ≤ 2^p`. The inverse transform is the forward
transform at the negated index. Bit costs and the per-term evaluation of the
negacyclic products are not modelled. -/

namespace IntegerMultBounds.NLogN

section Exact

variable {r : ℕ} [NeZero r]

/-- The normalised convolution `M_R(u, v) = (1/t) u ∗ v` of the paper. -/
noncomputable def synthConvNorm (n : ℕ) (u v : Fin (2 ^ n) → (Fin r → ℂ)) :
    Fin (2 ^ n) → (Fin r → ℂ) :=
  fun k => (1 / (2 ^ n : ℂ)) • synthConv (2 ^ n) u v k

theorem synthDFTInv_smul (t : ℕ) (c : ℂ) (u : Fin t → (Fin r → ℂ)) :
    synthDFTInv r t (fun j => c • u j) = fun j => c • synthDFTInv r t u j := by
  funext j
  simp only [synthDFTInv, shiftNegZ_smul, ← Finset.smul_sum, smul_comm c]

theorem synthDFTInv_sub (t : ℕ) (u v : Fin t → (Fin r → ℂ)) (j : Fin t) :
    synthDFTInv r t u j - synthDFTInv r t v j = synthDFTInv r t (fun k => u k - v k) j := by
  simp only [synthDFTInv, ← smul_sub, ← Finset.sum_sub_distrib]
  congr 2
  funext k
  rw [← shiftZCLM_apply, ← shiftZCLM_apply, ← shiftZCLM_apply, map_sub]

/-- The pipeline identity: `M_R(u, v) = (t r) F⁻¹((1/r) F u · F v)`. -/
theorem synthConvNorm_eq {n : ℕ} (hr : 2 ^ n ∣ 2 * r) (u v : Fin (2 ^ n) → (Fin r → ℂ)) :
    synthConvNorm n u v = fun j => ((2 ^ n : ℂ) * r) • synthDFTInv r (2 ^ n)
      (fun j => (1 / (r : ℂ)) • negacyclicMul (synthDFT r (2 ^ n) u j) (synthDFT r (2 ^ n) v j)) j := by
  have hinv := synthDFTInv_synthDFT hr rfl (synthConv (2 ^ n) u v)
  rw [synthDFT_conv hr] at hinv
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have h1 : (fun j => ((2 ^ n : ℕ) : ℂ) • negacyclicMul (synthDFT r (2 ^ n) u j)
      (synthDFT r (2 ^ n) v j))
      = fun j => (((2 ^ n : ℕ) : ℂ) * r) • ((1 / (r : ℂ)) •
        negacyclicMul (synthDFT r (2 ^ n) u j) (synthDFT r (2 ^ n) v j)) := by
    funext j
    rw [smul_smul]
    congr 1
    field_simp
  rw [h1, synthDFTInv_smul] at hinv
  funext j
  have := congrFun hinv j
  simp only [synthConvNorm, Nat.cast_pow, Nat.cast_ofNat] at this ⊢
  rw [← this]

omit [NeZero r] in
/-- Each of the `t` terms of the convolution has norm at most `r`. -/
theorem norm_synthConvNorm_le {n : ℕ} {u v : Fin (2 ^ n) → (Fin r → ℂ)}
    (hu : ∀ j, ‖u j‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1) (k : Fin (2 ^ n)) :
    ‖synthConvNorm n u v k‖ ≤ r := by
  simp only [synthConvNorm, synthConv]
  rw [norm_smul]
  have ht : ‖(1 / (2 ^ n : ℂ))‖ = 1 / 2 ^ n := by
    rw [norm_div, norm_one, norm_pow, Complex.norm_ofNat]
  rw [ht]
  have hsum : ‖∑ i : Fin (2 ^ n), negacyclicMul (u i) (v (k - i))‖ ≤ 2 ^ n * r := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i : Fin (2 ^ n), ‖negacyclicMul (u i) (v (k - i))‖ ≤ r := by
      intro i
      refine (norm_negacyclicMul_le _ _).trans ?_
      have h1 := hu i
      have h2 := hv (k - i)
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      calc (r : ℝ) * ‖u i‖ * ‖v (k - i)‖ ≤ r * 1 * 1 := by gcongr
        _ = r := by ring
    refine (Finset.sum_le_card_nsmul _ _ _ (fun i _ => this i)).trans ?_
    simp
  calc 1 / (2 : ℝ) ^ n * ‖∑ i : Fin (2 ^ n), negacyclicMul (u i) (v (k - i))‖
      ≤ 1 / 2 ^ n * (2 ^ n * r) := by gcongr
    _ = r := by field_simp

/-- The inverse transform is a contraction. -/
theorem norm_synthDFTInv_le {t : ℕ} [NeZero t] {A : ℝ} {u : Fin t → (Fin r → ℂ)}
    (hA : ∀ j, ‖u j‖ ≤ A) (k : Fin t) : ‖synthDFTInv r t u k‖ ≤ A := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA ⟨0, NeZero.pos t⟩)
  simp only [synthDFTInv]
  rw [norm_smul]
  have ht : ‖(1 / (t : ℂ))‖ = 1 / t := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [ht]
  have hsum : ‖∑ j : Fin t, shiftNegZ ((2 * r / t) * (t - 1) * k.val * j.val) (u j)‖ ≤ t * A := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _
      (fun j _ => (norm_shiftNegZ_le _ _).trans (hA j))).trans ?_
    simp
  have htpos : (0 : ℝ) < t := Nat.cast_pos.mpr (NeZero.pos t)
  calc 1 / (t : ℝ) * ‖∑ j : Fin t, shiftNegZ ((2 * r / t) * (t - 1) * k.val * j.val) (u j)‖
      ≤ 1 / t * (t * A) := by gcongr
    _ = A := by field_simp

/-- The normalised pointwise product is bounded by the product of the norms. -/
theorem norm_normProd_le (a b : Fin r → ℂ) :
    ‖(1 / (r : ℂ)) • negacyclicMul a b‖ ≤ ‖a‖ * ‖b‖ := by
  rw [norm_smul, norm_div, norm_one, Complex.norm_natCast]
  have hrpos : (0 : ℝ) < r := Nat.cast_pos.mpr (NeZero.pos r)
  calc 1 / (r : ℝ) * ‖negacyclicMul a b‖ ≤ 1 / r * (r * ‖a‖ * ‖b‖) := by
        gcongr; exact norm_negacyclicMul_le a b
    _ = ‖a‖ * ‖b‖ := by field_simp

theorem negacyclicMul_sub_left (a a' b : Fin r → ℂ) :
    negacyclicMul (a - a') b = negacyclicMul a b - negacyclicMul a' b := by
  rw [sub_eq_add_neg, negacyclicMul_add_left, ← neg_one_smul ℂ a', negacyclicMul_smul_left,
    neg_one_smul, ← sub_eq_add_neg]

theorem negacyclicMul_sub_right (a b b' : Fin r → ℂ) :
    negacyclicMul a (b - b') = negacyclicMul a b - negacyclicMul a b' := by
  rw [negacyclicMul_comm, negacyclicMul_sub_left, negacyclicMul_comm, negacyclicMul_comm b']

/-- The bilinear error bound for the normalised pointwise product. -/
theorem normProd_err {a a' b b' : Fin r → ℂ} {δ : ℝ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (ha' : ‖a' - a‖ ≤ δ) (hb' : ‖b' - b‖ ≤ δ) :
    ‖(1 / (r : ℂ)) • negacyclicMul a' b' - (1 / (r : ℂ)) • negacyclicMul a b‖
      ≤ 2 * δ + δ ^ 2 := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans ha'
  have hsplit : negacyclicMul a' b' - negacyclicMul a b
      = negacyclicMul (a' - a) b' + negacyclicMul a (b' - b) := by
    rw [negacyclicMul_sub_left, negacyclicMul_sub_right]; abel
  rw [← smul_sub, hsplit, smul_add]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_normProd_le (a' - a) b'
  have h2 := norm_normProd_le a (b' - b)
  have hb'n : ‖b'‖ ≤ 1 + δ := by
    calc ‖b'‖ = ‖(b' - b) + b‖ := by rw [sub_add_cancel]
      _ ≤ ‖b' - b‖ + ‖b‖ := norm_add_le _ _
      _ ≤ δ + 1 := by gcongr
      _ = 1 + δ := by ring
  calc ‖(1 / (r : ℂ)) • negacyclicMul (a' - a) b'‖ + ‖(1 / (r : ℂ)) • negacyclicMul a (b' - b)‖
      ≤ ‖a' - a‖ * ‖b'‖ + ‖a‖ * ‖b' - b‖ := add_le_add h1 h2
    _ ≤ δ * (1 + δ) + 1 * δ := by gcongr
    _ = 2 * δ + δ ^ 2 := by ring

/-- `(t - 1) j ≡ -j (mod t)` as values in `Fin t`. -/
theorem sub_one_mul_val_mod {t : ℕ} [NeZero t] (j : Fin t) :
    ((t - 1) * j.val) % t = (-j).val := by
  rw [Fin.val_neg']
  have hj := j.isLt
  have htpos := NeZero.pos t
  have h : Nat.ModEq t ((t - 1) * j.val + j.val) ((t - j.val) + j.val) := by
    have e1 : (t - 1) * j.val + j.val = t * j.val := by
      rw [Nat.sub_one_mul]; have := Nat.le_mul_of_pos_left j.val htpos; omega
    have e2 : t - j.val + j.val = t := by omega
    rw [e1, e2]
    exact (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right t _)).trans
      (Nat.modEq_zero_iff_dvd.mpr dvd_rfl).symm
  exact Nat.ModEq.add_right_cancel' j.val h

/-- The inverse transform is the forward transform at the negated index. -/
theorem synthDFTInv_eq {t : ℕ} [NeZero t] (hr : t ∣ 2 * r) (u : Fin t → (Fin r → ℂ)) (j : Fin t) :
    synthDFTInv r t u j = synthDFT r t u (-j) := by
  simp only [synthDFTInv, synthDFT]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have e1 : (2 * r / t) * (t - 1) * j.val * k.val = (2 * r / t) * k.val * ((t - 1) * j.val) := by
    ring
  have e2 : (2 * r / t) * (-j).val * k.val = (2 * r / t) * k.val * (-j).val := by ring
  rw [e1, e2, shiftNegZ_mul_mod hr, sub_one_mul_val_mod]

/-- Linearity of the forward transform in difference form. -/
theorem synthDFT_sub {n : ℕ} (hr : 2 ^ n ∣ 2 * r) (u v : Fin (2 ^ n) → (Fin r → ℂ))
    (k : Fin (2 ^ n)) :
    synthDFT r (2 ^ n) u k - synthDFT r (2 ^ n) v k = synthDFT r (2 ^ n) (fun j => u j - v j) k := by
  rw [← fftNorm_synth n hr, ← fftNorm_synth n hr, ← fftNorm_synth n hr]
  exact fftNorm_sub n _ u v k

end Exact

section Rounding

/-- Componentwise rounding toward zero at `p` bits. -/
noncomputable def rdC (p : ℕ) {ι : Type*} (x : ι → ℂ) : ι → ℂ := fun i => rhoC p (x i)

theorem norm_rdC_sub_le (p : ℕ) {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    ‖rdC p x - x‖ ≤ 2 / 2 ^ p := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  exact norm_rhoC_sub_le_two p (x i)

theorem norm_rdC_le (p : ℕ) {ι : Type*} [Fintype ι] (x : ι → ℂ) : ‖rdC p x‖ ≤ ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  exact (norm_rhoC_le p (x i)).trans (norm_le_pi_norm x i)

end Rounding

section Pipeline

variable {r : ℕ} [NeZero r]

/-- The exact normalised pipeline before the final scaling by `t r`. -/
noncomputable def synthPipeExact (n : ℕ) (u v : Fin (2 ^ n) → (Fin r → ℂ)) :
    Fin (2 ^ n) → (Fin r → ℂ) :=
  synthDFTInv r (2 ^ n)
    (fun j => (1 / (r : ℂ)) • negacyclicMul (synthDFT r (2 ^ n) u j) (synthDFT r (2 ^ n) v j))

/-- The pipeline with error oracles in the three transforms and rounded products. -/
noncomputable def synthPipeApprox (n p : ℕ)
    (e₁ e₂ e₃ : (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ))
    (u v : Fin (2 ^ n) → (Fin r → ℂ)) : Fin (2 ^ n) → (Fin r → ℂ) :=
  let Fu := fftNormErr n (wSynth r n) e₁ u
  let Fv := fftNormErr n (wSynth r n) e₂ v
  let z := fun j => rdC p ((1 / (r : ℂ)) • negacyclicMul (Fu j) (Fv j))
  fun j => fftNormErr n (wSynth r n) e₃ z (-j)

/-- Proposition 3.4 before scaling: absolute error `(3n + 2)/2^p + (n/2^p)^2`. -/
theorem synthPipe_err {n p : ℕ} (hr : 2 ^ n ∣ 2 * r)
    {e₁ e₂ e₃ : (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)}
    (he₁ : ∀ m k, ‖e₁ m k‖ ≤ 1 / 2 ^ p) (he₂ : ∀ m k, ‖e₂ m k‖ ≤ 1 / 2 ^ p)
    (he₃ : ∀ m k, ‖e₃ m k‖ ≤ 1 / 2 ^ p)
    {u v : Fin (2 ^ n) → (Fin r → ℂ)} (hu : ∀ j, ‖u j‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1)
    (j : Fin (2 ^ n)) :
    ‖synthPipeApprox n p e₁ e₂ e₃ u v j - synthPipeExact n u v j‖
      ≤ (3 * n + 2) / 2 ^ p + (n / 2 ^ p) ^ 2 := by
  set δ : ℝ := n / 2 ^ p with hδ
  have hδ0 : 0 ≤ δ := by positivity
  set Fu' := fftNormErr n (wSynth r n) e₁ u
  set Fv' := fftNormErr n (wSynth r n) e₂ v
  set Fu := synthDFT r (2 ^ n) u
  set Fv := synthDFT r (2 ^ n) v
  set z' : Fin (2 ^ n) → (Fin r → ℂ) :=
    fun j => rdC p ((1 / (r : ℂ)) • negacyclicMul (Fu' j) (Fv' j))
  set z : Fin (2 ^ n) → (Fin r → ℂ) :=
    fun j => (1 / (r : ℂ)) • negacyclicMul (Fu j) (Fv j)
  -- forward transform errors
  have hFu : ∀ j, ‖Fu' j - Fu j‖ ≤ δ := fun j => by
    have := synth_fft_err hr he₁ u j
    rw [hδ, div_eq_mul_one_div]; exact this
  have hFv : ∀ j, ‖Fv' j - Fv j‖ ≤ δ := fun j => by
    have := synth_fft_err hr he₂ v j
    rw [hδ, div_eq_mul_one_div]; exact this
  have hFu1 : ∀ j, ‖Fu j‖ ≤ 1 := fun j => norm_synthDFT_le hr hu j
  have hFv1 : ∀ j, ‖Fv j‖ ≤ 1 := fun j => norm_synthDFT_le hr hv j
  -- pointwise product and rounding errors
  have hz : ∀ j, ‖z' j - z j‖ ≤ 2 / 2 ^ p + (2 * δ + δ ^ 2) := by
    intro j
    set x := (1 / (r : ℂ)) • negacyclicMul (Fu' j) (Fv' j)
    calc ‖z' j - z j‖ = ‖(rdC p x - x) + (x - z j)‖ := by
          simp only [z', z, x]; congr 1; abel
      _ ≤ ‖rdC p x - x‖ + ‖x - z j‖ := norm_add_le _ _
      _ ≤ 2 / 2 ^ p + (2 * δ + δ ^ 2) := by
          gcongr
          · exact norm_rdC_sub_le p x
          · exact normProd_err (hFu1 j) (hFv1 j) (hFu j) (hFv j)
  -- inverse transform
  have hexact : synthPipeExact n u v j = synthDFT r (2 ^ n) z (-j) := by
    simp only [synthPipeExact]
    exact synthDFTInv_eq hr z j
  have happrox : synthPipeApprox n p e₁ e₂ e₃ u v j = fftNormErr n (wSynth r n) e₃ z' (-j) := rfl
  rw [hexact, happrox]
  calc ‖fftNormErr n (wSynth r n) e₃ z' (-j) - synthDFT r (2 ^ n) z (-j)‖
      = ‖(fftNormErr n (wSynth r n) e₃ z' (-j) - synthDFT r (2 ^ n) z' (-j))
          + (synthDFT r (2 ^ n) z' (-j) - synthDFT r (2 ^ n) z (-j))‖ := by
        congr 1; abel
    _ ≤ ‖fftNormErr n (wSynth r n) e₃ z' (-j) - synthDFT r (2 ^ n) z' (-j)‖
          + ‖synthDFT r (2 ^ n) z' (-j) - synthDFT r (2 ^ n) z (-j)‖ := norm_add_le _ _
    _ ≤ δ + (2 / 2 ^ p + (2 * δ + δ ^ 2)) := by
        gcongr
        · have := synth_fft_err hr he₃ z' (-j); rw [hδ, div_eq_mul_one_div]; exact this
        · rw [synthDFT_sub hr]
          exact norm_synthDFT_le hr hz (-j)
    _ = (3 * n + 2) / 2 ^ p + (n / 2 ^ p) ^ 2 := by
        rw [hδ]; ring

/-- Proposition 3.4: the scaled pipeline approximates `M_R(u, v)` with absolute
error `t r ((3n + 2)/2^p + (n/2^p)^2)`. -/
theorem synthConvNorm_approx {n p : ℕ} (hr : 2 ^ n ∣ 2 * r)
    {e₁ e₂ e₃ : (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)}
    (he₁ : ∀ m k, ‖e₁ m k‖ ≤ 1 / 2 ^ p) (he₂ : ∀ m k, ‖e₂ m k‖ ≤ 1 / 2 ^ p)
    (he₃ : ∀ m k, ‖e₃ m k‖ ≤ 1 / 2 ^ p)
    {u v : Fin (2 ^ n) → (Fin r → ℂ)} (hu : ∀ j, ‖u j‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1)
    (j : Fin (2 ^ n)) :
    ‖((2 ^ n : ℂ) * r) • synthPipeApprox n p e₁ e₂ e₃ u v j - synthConvNorm n u v j‖
      ≤ 2 ^ n * r * ((3 * n + 2) / 2 ^ p + (n / 2 ^ p) ^ 2) := by
  rw [synthConvNorm_eq hr]
  have h := synthPipe_err hr he₁ he₂ he₃ hu hv j
  simp only [synthPipeExact] at h
  rw [← smul_sub, norm_smul, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_natCast]
  gcongr

/-- Scaled error `4n + 2` once `n ≤ 2^p`. -/
theorem synthPipe_err_scaled {n p : ℕ} (hr : 2 ^ n ∣ 2 * r) (hn : (n : ℝ) ≤ 2 ^ p)
    {e₁ e₂ e₃ : (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)}
    (he₁ : ∀ m k, ‖e₁ m k‖ ≤ 1 / 2 ^ p) (he₂ : ∀ m k, ‖e₂ m k‖ ≤ 1 / 2 ^ p)
    (he₃ : ∀ m k, ‖e₃ m k‖ ≤ 1 / 2 ^ p)
    {u v : Fin (2 ^ n) → (Fin r → ℂ)} (hu : ∀ j, ‖u j‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1)
    (j : Fin (2 ^ n)) :
    2 ^ p * ‖synthPipeApprox n p e₁ e₂ e₃ u v j - synthPipeExact n u v j‖ ≤ 4 * n + 2 := by
  have h := synthPipe_err hr he₁ he₂ he₃ hu hv j
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hsq : (n / 2 ^ p : ℝ) ^ 2 ≤ n / 2 ^ p := by
    have h1 : (n / 2 ^ p : ℝ) ≤ 1 := by rw [div_le_one hp]; exact hn
    have h0 : (0 : ℝ) ≤ n / 2 ^ p := by positivity
    nlinarith
  have h' := h.trans (add_le_add le_rfl hsq)
  calc 2 ^ p * ‖synthPipeApprox n p e₁ e₂ e₃ u v j - synthPipeExact n u v j‖
      ≤ 2 ^ p * ((3 * n + 2) / 2 ^ p + n / 2 ^ p) := by gcongr
    _ = 4 * n + 2 := by field_simp; ring

end Pipeline

end IntegerMultBounds.NLogN
