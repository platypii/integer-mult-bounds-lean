import IntegerMultBounds.NLogN.SynthMultiD
import IntegerMultBounds.NLogN.SynthConvApprox
import IntegerMultBounds.NLogN.TensorApproxV

/-! Propositions 3.3 and 3.4 of Harvey and van der Hoeven in `d` dimensions
over the synthetic ring in coefficient form. The `d`-dimensional synthetic
transform is the tensor of the one-dimensional transforms, hence a contraction
packaged as a continuous linear map; computing it coordinate by coordinate with
the one-dimensional synthetic FFTs and per-level error oracles of size `2^(-p)`
gives scaled error at most `∑ log₂ t_i = log₂ T'`. The inverse transform is the
forward transform at the negated index. The convolution pipeline (two forward
transforms, `1/r`-scaled pointwise negacyclic products with componentwise
rounding, inverse transform) has scaled error at most `3 log₂ T' + 2` before
the final scaling by `T' r`, and after scaling approximates the normalised
convolution `(1/T') u ∗ v` with absolute error `T' r (3 log₂ T' + 2)/2^p`.
The numerical transforms are assumed to map the unit ball into itself (the
paper's `C̃◦` convention, obtained by clamping); bit costs are not modelled. -/

namespace IntegerMultBounds.NLogN

section Tensor

variable {r : ℕ} [NeZero r] {d : ℕ}

/-- The `d`-dimensional synthetic transform is the tensor of the one-dimensional ones. -/
theorem synthDFTD_eq_tensorV : ∀ (d : ℕ) (N : Fin d → ℕ) [∀ i, NeZero (N i)]
    (u : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)),
    synthDFTD r N u = tensorV d N (fun i => synthDFT r (N i)) u
  | 0, N, _, u => by
    funext j
    simp only [synthDFTD, Finset.univ_unique, Finset.sum_singleton, Fin.prod_univ_zero,
      Nat.cast_one, div_one, one_smul, tensorV, id]
    have hexp : ∀ k, synthExp r N j k = 0 := fun k => by simp [synthExp]
    simp only [hexp, shiftNegZ_zero]
    exact congrArg _ (Subsingleton.elim _ _)
  | d + 1, N, _, u => by
    rw [synthDFTD_succ, tensorV_succ]
    funext k
    simp only [alongHeadV, alongTailV, Fin.cons_zero, Fin.tail_cons]
    congr 1
    funext j₀
    exact congrFun (synthDFTD_eq_tensorV d (fun i => N i.succ) (fun k' => u (Fin.cons j₀ k')))
      (Fin.tail k)

/-- The one-dimensional synthetic transform as a continuous linear map. -/
noncomputable def synthDFTCLM (r : ℕ) [NeZero r] (t : ℕ) :
    (Fin t → (Fin r → ℂ)) →L[ℂ] (Fin t → (Fin r → ℂ)) :=
  ContinuousLinearMap.pi fun j => (1 / (t : ℂ)) •
    ∑ k, (shiftZCLM r ((2 * r / t) * j.val * k.val)).comp (ContinuousLinearMap.proj k)

theorem synthDFTCLM_apply (t : ℕ) (u : Fin t → (Fin r → ℂ)) :
    synthDFTCLM r t u = synthDFT r t u := by
  funext j
  simp [synthDFTCLM, synthDFT, shiftZCLM_apply]

/-- The synthetic transform of any positive length is a contraction. -/
theorem norm_synthDFT_le_of_le {t : ℕ} [NeZero t] {A : ℝ} {u : Fin t → (Fin r → ℂ)}
    (hA : ∀ j, ‖u j‖ ≤ A) (k : Fin t) : ‖synthDFT r t u k‖ ≤ A := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA ⟨0, NeZero.pos t⟩)
  simp only [synthDFT]
  rw [norm_smul]
  have ht : ‖(1 / (t : ℂ))‖ = 1 / t := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [ht]
  have hsum : ‖∑ j : Fin t, shiftNegZ ((2 * r / t) * k.val * j.val) (u j)‖ ≤ t * A := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _
      (fun j _ => (norm_shiftNegZ_le _ _).trans (hA j))).trans ?_
    simp
  have htpos : (0 : ℝ) < t := Nat.cast_pos.mpr (NeZero.pos t)
  calc 1 / (t : ℝ) * ‖∑ j : Fin t, shiftNegZ ((2 * r / t) * k.val * j.val) (u j)‖
      ≤ 1 / t * (t * A) := by gcongr
    _ = A := by field_simp

theorem opNorm_synthDFTCLM_le (t : ℕ) [NeZero t] : ‖synthDFTCLM r t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [synthDFTCLM_apply, one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro k
  exact norm_synthDFT_le_of_le (fun j => norm_le_pi_norm u j) k

/-- The `d`-dimensional synthetic transform as a continuous linear map. -/
noncomputable def synthDFTDCLM (r : ℕ) [NeZero r] (N : Fin d → ℕ) :
    (((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) →L[ℂ] (((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) :=
  tensorVCLM d N fun i => synthDFTCLM r (N i)

theorem synthDFTDCLM_apply (N : Fin d → ℕ) [∀ i, NeZero (N i)]
    (u : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) :
    synthDFTDCLM r N u = synthDFTD r N u := by
  rw [synthDFTDCLM, tensorVCLM_apply, synthDFTD_eq_tensorV]
  congr 1
  funext i v
  exact synthDFTCLM_apply (N i) v

theorem opNorm_synthDFTDCLM_le (N : Fin d → ℕ) [∀ i, NeZero (N i)] :
    ‖synthDFTDCLM r N‖ ≤ 1 :=
  opNorm_tensorVCLM_le d N _ fun i => opNorm_synthDFTCLM_le (N i)

omit [NeZero r] in
/-- The inverse transform is the forward transform at the negated index. -/
theorem synthDFTDInv_eq (N : Fin d → ℕ) [∀ i, NeZero (N i)]
    (u : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) (j : (i : Fin d) → Fin (N i)) :
    synthDFTDInv r N u j = synthDFTD r N u (-j) := rfl

/-- Linearity of the `d`-dimensional transform in difference form. -/
theorem synthDFTD_sub_apply (N : Fin d → ℕ) [∀ i, NeZero (N i)]
    (u v : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) (j : (i : Fin d) → Fin (N i)) :
    synthDFTD r N u j - synthDFTD r N v j = synthDFTD r N (fun k => u k - v k) j := by
  simp only [synthDFTD, ← smul_sub, ← Finset.sum_sub_distrib]
  congr 2
  funext k
  rw [← shiftZCLM_apply, ← shiftZCLM_apply, ← shiftZCLM_apply, map_sub]

theorem synthDFTDInv_const_smul (N : Fin d → ℕ) [∀ i, NeZero (N i)] (c : ℂ)
    (u : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) :
    synthDFTDInv r N (fun j => c • u j) = fun j => c • synthDFTDInv r N u j := by
  funext j
  simp only [synthDFTDInv, shiftNegZ_smul, ← Finset.smul_sum, smul_comm c]

end Tensor

section Numeric

variable {r : ℕ} [NeZero r] {d : ℕ}

/-- The numerical `d`-dimensional synthetic transform: the one-dimensional
synthetic FFTs with error oracles `E i`, applied coordinate by coordinate. -/
noncomputable def synthDFTDNum (r : ℕ) [NeZero r] (e : Fin d → ℕ)
    (E : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)) :
    (((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ)) → (((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ)) :=
  tensorV d (fun i => 2 ^ e i) fun i => fftNormErr (e i) (wSynth r (e i)) (E i)

/-- Lemma 3.2 packaged: the one-dimensional synthetic FFT with oracles of size
`2^(-p)` approximates the transform of length `2^n` with scaled error `n`. -/
theorem approxMap_synthFFT {n p : ℕ} (hr : 2 ^ n ∣ 2 * r)
    {E : (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)} (hE : ∀ m k, ‖E m k‖ ≤ 1 / 2 ^ p) :
    ApproxMap p (fftNormErr n (wSynth r n) E) (synthDFTCLM r (2 ^ n)) n := by
  intro u _
  rw [synthDFTCLM_apply]
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have : ‖fftNormErr n (wSynth r n) E u - synthDFT r (2 ^ n) u‖ ≤ n / 2 ^ p := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    have := synth_fft_err hr hE u k
    rw [div_eq_mul_one_div]
    exact this
  calc (2 : ℝ) ^ p * ‖fftNormErr n (wSynth r n) E u - synthDFT r (2 ^ n) u‖
      ≤ 2 ^ p * (n / 2 ^ p) := by gcongr
    _ = n := by field_simp

/-- Proposition 3.3: the coordinatewise numerical transform has scaled error
`∑ log₂ t_i`, given that each one-dimensional FFT keeps the unit ball. -/
theorem approxMap_synthDFTDNum {p : ℕ} (e : Fin d → ℕ) (hr : ∀ i, 2 ^ e i ∣ 2 * r)
    {E : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)}
    (hE : ∀ i m k, ‖E i m k‖ ≤ 1 / 2 ^ p)
    (hball : ∀ i u, ‖u‖ ≤ 1 → ‖fftNormErr (e i) (wSynth r (e i)) (E i) u‖ ≤ 1) :
    ApproxMap p (synthDFTDNum r e E) (synthDFTDCLM r fun i => 2 ^ e i) (∑ i, (e i : ℝ)) :=
  approxMap_tensorV d _ _ _ _ (fun i => opNorm_synthDFTCLM_le (2 ^ e i))
    (fun i => approxMap_synthFFT (hr i) (hE i)) hball

theorem synthDFTDNum_ball {e : Fin d → ℕ}
    {E : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)}
    (hball : ∀ i u, ‖u‖ ≤ 1 → ‖fftNormErr (e i) (wSynth r (e i)) (E i) u‖ ≤ 1)
    (u : ((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ)) (hu : ‖u‖ ≤ 1) :
    ‖synthDFTDNum r e E u‖ ≤ 1 :=
  tensorV_ball d _ _ hball u hu

end Numeric

section Pipeline

variable {r : ℕ} [NeZero r] {d : ℕ}

/-- The bilinear error bound for the normalised pointwise product on the unit ball. -/
theorem normProd_err_ball {a a' b b' : Fin r → ℂ} {δ : ℝ} (ha : ‖a‖ ≤ 1) (hb' : ‖b'‖ ≤ 1)
    (ha' : ‖a' - a‖ ≤ δ) (hbb' : ‖b' - b‖ ≤ δ) :
    ‖(1 / (r : ℂ)) • negacyclicMul a' b' - (1 / (r : ℂ)) • negacyclicMul a b‖ ≤ 2 * δ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans ha'
  have hsplit : negacyclicMul a' b' - negacyclicMul a b
      = negacyclicMul (a' - a) b' + negacyclicMul a (b' - b) := by
    rw [negacyclicMul_sub_left, negacyclicMul_sub_right]; abel
  rw [← smul_sub, hsplit, smul_add]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_normProd_le (a' - a) b'
  have h2 := norm_normProd_le a (b' - b)
  calc ‖(1 / (r : ℂ)) • negacyclicMul (a' - a) b'‖ + ‖(1 / (r : ℂ)) • negacyclicMul a (b' - b)‖
      ≤ ‖a' - a‖ * ‖b'‖ + ‖a‖ * ‖b' - b‖ := add_le_add h1 h2
    _ ≤ δ * 1 + 1 * δ := by gcongr
    _ = 2 * δ := by ring

/-- The exact normalised pipeline before the final scaling by `T' r`. -/
noncomputable def synthPipeDExact (r : ℕ) [NeZero r] (e : Fin d → ℕ)
    (u v : ((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ)) :
    ((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ) :=
  synthDFTDInv r (fun i => 2 ^ e i) fun j =>
    (1 / (r : ℂ)) • negacyclicMul (synthDFTD r (fun i => 2 ^ e i) u j)
      (synthDFTD r (fun i => 2 ^ e i) v j)

/-- The numerical pipeline: numerical forward transforms, rounded `1/r`-scaled
products, numerical inverse transform (the forward one at the negated index). -/
noncomputable def synthPipeDNum (r : ℕ) [NeZero r] (e : Fin d → ℕ) (p : ℕ)
    (E₁ E₂ E₃ : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ))
    (u v : ((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ)) :
    ((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ) :=
  let Fu := synthDFTDNum r e E₁ u
  let Fv := synthDFTDNum r e E₂ v
  let z := fun j => rdC p ((1 / (r : ℂ)) • negacyclicMul (Fu j) (Fv j))
  fun j => synthDFTDNum r e E₃ z (-j)

/-- Proposition 3.4 before scaling: scaled error `3 ∑ log₂ t_i + 2`. -/
theorem synthPipeD_err {p : ℕ} (e : Fin d → ℕ) (hr : ∀ i, 2 ^ e i ∣ 2 * r)
    {E₁ E₂ E₃ : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)}
    (hE₁ : ∀ i m k, ‖E₁ i m k‖ ≤ 1 / 2 ^ p) (hE₂ : ∀ i m k, ‖E₂ i m k‖ ≤ 1 / 2 ^ p)
    (hE₃ : ∀ i m k, ‖E₃ i m k‖ ≤ 1 / 2 ^ p)
    (hball₁ : ∀ i u, ‖u‖ ≤ 1 → ‖fftNormErr (e i) (wSynth r (e i)) (E₁ i) u‖ ≤ 1)
    (hball₂ : ∀ i u, ‖u‖ ≤ 1 → ‖fftNormErr (e i) (wSynth r (e i)) (E₂ i) u‖ ≤ 1)
    (hball₃ : ∀ i u, ‖u‖ ≤ 1 → ‖fftNormErr (e i) (wSynth r (e i)) (E₃ i) u‖ ≤ 1)
    {u v : ((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ)} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (j : (i : Fin d) → Fin (2 ^ e i)) :
    2 ^ p * ‖synthPipeDNum r e p E₁ E₂ E₃ u v j - synthPipeDExact r e u v j‖
      ≤ 3 * (∑ i, (e i : ℝ)) + 2 := by
  set S : ℝ := ∑ i, (e i : ℝ) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set δ : ℝ := S / 2 ^ p with hδ
  have hδ0 : 0 ≤ δ := by positivity
  set N : Fin d → ℕ := fun i => 2 ^ e i with hN
  set Fu' := synthDFTDNum r e E₁ u
  set Fv' := synthDFTDNum r e E₂ v
  set Fu := synthDFTD r N u
  set Fv := synthDFTD r N v
  set z' : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ) :=
    fun j => rdC p ((1 / (r : ℂ)) • negacyclicMul (Fu' j) (Fv' j))
  set z : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ) :=
    fun j => (1 / (r : ℂ)) • negacyclicMul (Fu j) (Fv j)
  -- scaled error of the numerical transform, elementwise
  have herr : ∀ (E : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)),
      (∀ i m k, ‖E i m k‖ ≤ 1 / 2 ^ p) →
      (∀ i u, ‖u‖ ≤ 1 → ‖fftNormErr (e i) (wSynth r (e i)) (E i) u‖ ≤ 1) →
      ∀ w : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ), ‖w‖ ≤ 1 →
      ∀ k, ‖synthDFTDNum r e E w k - synthDFTD r N w k‖ ≤ δ := by
    intro E hE hball w hw k
    have h := approxMap_synthDFTDNum e hr hE hball w hw
    rw [synthDFTDCLM_apply] at h
    have h' : ‖synthDFTDNum r e E w - synthDFTD r N w‖ ≤ δ := by
      rw [hδ, le_div_iff₀ hp, mul_comm]
      exact h
    exact (norm_le_pi_norm _ k).trans h'
  have hFu : ∀ k, ‖Fu' k - Fu k‖ ≤ δ := herr E₁ hE₁ hball₁ u hu
  have hFv : ∀ k, ‖Fv' k - Fv k‖ ≤ δ := herr E₂ hE₂ hball₂ v hv
  have hFu1 : ∀ k, ‖Fu k‖ ≤ 1 := fun k =>
    norm_synthDFTD_le (fun j => norm_le_pi_norm u j |>.trans hu) k
  have hFv'1 : ∀ k, ‖Fv' k‖ ≤ 1 := fun k =>
    (norm_le_pi_norm _ k).trans (synthDFTDNum_ball hball₂ v hv)
  have hFu'1 : ∀ k, ‖Fu' k‖ ≤ 1 := fun k =>
    (norm_le_pi_norm _ k).trans (synthDFTDNum_ball hball₁ u hu)
  -- pointwise product and rounding errors
  have hz : ∀ k, ‖z' k - z k‖ ≤ 2 / 2 ^ p + 2 * δ := by
    intro k
    set x := (1 / (r : ℂ)) • negacyclicMul (Fu' k) (Fv' k)
    calc ‖z' k - z k‖ = ‖(rdC p x - x) + (x - z k)‖ := by
          simp only [z', z, x]; congr 1; abel
      _ ≤ ‖rdC p x - x‖ + ‖x - z k‖ := norm_add_le _ _
      _ ≤ 2 / 2 ^ p + 2 * δ := by
          gcongr
          · exact norm_rdC_sub_le p x
          · exact normProd_err_ball (hFu1 k) (hFv'1 k) (hFu k) (hFv k)
  have hz'1 : ‖z'‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    refine (norm_rdC_le p _).trans ?_
    refine (norm_normProd_le _ _).trans ?_
    calc ‖Fu' k‖ * ‖Fv' k‖ ≤ 1 * 1 := by gcongr; exacts [hFu'1 k, hFv'1 k]
      _ = 1 := one_mul 1
  -- inverse transform
  have hexact : synthPipeDExact r e u v j = synthDFTD r N z (-j) := rfl
  have happrox : synthPipeDNum r e p E₁ E₂ E₃ u v j = synthDFTDNum r e E₃ z' (-j) := rfl
  rw [hexact, happrox]
  have hsub : ∀ k, ‖synthDFTD r N z' k - synthDFTD r N z k‖ ≤ 2 / 2 ^ p + 2 * δ := by
    intro k
    rw [synthDFTD_sub_apply]
    exact norm_synthDFTD_le hz k
  have htotal : ‖synthDFTDNum r e E₃ z' (-j) - synthDFTD r N z (-j)‖
      ≤ δ + (2 / 2 ^ p + 2 * δ) := by
    calc ‖synthDFTDNum r e E₃ z' (-j) - synthDFTD r N z (-j)‖
        = ‖(synthDFTDNum r e E₃ z' (-j) - synthDFTD r N z' (-j))
            + (synthDFTD r N z' (-j) - synthDFTD r N z (-j))‖ := by
          congr 1; abel
      _ ≤ ‖synthDFTDNum r e E₃ z' (-j) - synthDFTD r N z' (-j)‖
            + ‖synthDFTD r N z' (-j) - synthDFTD r N z (-j)‖ := norm_add_le _ _
      _ ≤ δ + (2 / 2 ^ p + 2 * δ) := add_le_add (herr E₃ hE₃ hball₃ z' hz'1 (-j)) (hsub (-j))
  calc 2 ^ p * ‖synthDFTDNum r e E₃ z' (-j) - synthDFTD r N z (-j)‖
      ≤ 2 ^ p * (δ + (2 / 2 ^ p + 2 * δ)) := by gcongr
    _ = 3 * S + 2 := by rw [hδ]; field_simp; ring

/-- The pipeline identity in `d` dimensions:
`(1/T') u ∗ v = (T' r) F⁻¹((1/r) F u · F v)`. -/
theorem synthConvD_pipeline_eq (e : Fin d → ℕ) (hr : ∀ i, 2 ^ e i ∣ 2 * r)
    (u v : ((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ)) :
    (fun j => (1 / ((∏ i, 2 ^ e i : ℕ) : ℂ)) • synthConvG u v j)
      = fun j => (((∏ i, 2 ^ e i : ℕ) : ℂ) * r) • synthPipeDExact r e u v j := by
  set N : Fin d → ℕ := fun i => 2 ^ e i with hN
  have hpow : ∀ i, ∃ f, N i = 2 ^ f := fun i => ⟨e i, rfl⟩
  have hinv := synthDFTDInv_synthDFTD (r := r) (N := N) hr hpow (synthConvG u v)
  rw [synthDFTD_conv hr] at hinv
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have h1 : (fun j => ((∏ i, N i : ℕ) : ℂ) • negacyclicMul (synthDFTD r N u j) (synthDFTD r N v j))
      = fun j => (((∏ i, N i : ℕ) : ℂ) * r) • ((1 / (r : ℂ)) •
        negacyclicMul (synthDFTD r N u j) (synthDFTD r N v j)) := by
    funext j
    rw [smul_smul]
    congr 1
    field_simp
  rw [h1, synthDFTDInv_const_smul] at hinv
  funext j
  have := congrFun hinv j
  simp only [synthPipeDExact]
  exact this.symm

omit [NeZero r] in
/-- Each entry of the normalised convolution has norm at most `r` on unit balls. -/
theorem norm_synthConvG_div_le (e : Fin d → ℕ)
    {u v : ((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ)} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (k : (i : Fin d) → Fin (2 ^ e i)) :
    ‖(1 / ((∏ i, 2 ^ e i : ℕ) : ℂ)) • synthConvG u v k‖ ≤ r := by
  have hT : (0 : ℝ) < (∏ i, 2 ^ e i : ℕ) := by positivity
  rw [norm_smul, norm_div, norm_one, Complex.norm_natCast]
  have hsum : ‖synthConvG u v k‖ ≤ (∏ i, 2 ^ e i : ℕ) * r := by
    simp only [synthConvG]
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i, ‖negacyclicMul (u i) (v (k - i))‖ ≤ r := by
      intro i
      refine (norm_negacyclicMul_le _ _).trans ?_
      have h1 := (norm_le_pi_norm u i).trans hu
      have h2 := (norm_le_pi_norm v (k - i)).trans hv
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      calc (r : ℝ) * ‖u i‖ * ‖v (k - i)‖ ≤ r * 1 * 1 := by gcongr
        _ = r := by ring
    refine (Finset.sum_le_card_nsmul _ _ _ (fun i _ => this i)).trans ?_
    simp [Fintype.card_pi]
  calc 1 / ((∏ i, 2 ^ e i : ℕ) : ℝ) * ‖synthConvG u v k‖
      ≤ 1 / ((∏ i, 2 ^ e i : ℕ) : ℝ) * ((∏ i, 2 ^ e i : ℕ) * r) := by gcongr
    _ = r := by field_simp

/-- Proposition 3.4: after the final scaling the numerical pipeline approximates
the normalised convolution `(1/T') u ∗ v` with absolute error
`T' r (3 ∑ log₂ t_i + 2) / 2^p`. -/
theorem synthConvNormD_approx {p : ℕ} (e : Fin d → ℕ) (hr : ∀ i, 2 ^ e i ∣ 2 * r)
    {E₁ E₂ E₃ : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)}
    (hE₁ : ∀ i m k, ‖E₁ i m k‖ ≤ 1 / 2 ^ p) (hE₂ : ∀ i m k, ‖E₂ i m k‖ ≤ 1 / 2 ^ p)
    (hE₃ : ∀ i m k, ‖E₃ i m k‖ ≤ 1 / 2 ^ p)
    (hball₁ : ∀ i u, ‖u‖ ≤ 1 → ‖fftNormErr (e i) (wSynth r (e i)) (E₁ i) u‖ ≤ 1)
    (hball₂ : ∀ i u, ‖u‖ ≤ 1 → ‖fftNormErr (e i) (wSynth r (e i)) (E₂ i) u‖ ≤ 1)
    (hball₃ : ∀ i u, ‖u‖ ≤ 1 → ‖fftNormErr (e i) (wSynth r (e i)) (E₃ i) u‖ ≤ 1)
    {u v : ((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ)} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (j : (i : Fin d) → Fin (2 ^ e i)) :
    ‖(((∏ i, 2 ^ e i : ℕ) : ℂ) * r) • synthPipeDNum r e p E₁ E₂ E₃ u v j
        - (1 / ((∏ i, 2 ^ e i : ℕ) : ℂ)) • synthConvG u v j‖
      ≤ (∏ i, 2 ^ e i : ℕ) * r * ((3 * (∑ i, (e i : ℝ)) + 2) / 2 ^ p) := by
  have hpipe := congrFun (synthConvD_pipeline_eq e hr u v) j
  rw [hpipe, ← smul_sub, norm_smul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have h := synthPipeD_err e hr hE₁ hE₂ hE₃ hball₁ hball₂ hball₃ hu hv j
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h' : ‖synthPipeDNum r e p E₁ E₂ E₃ u v j - synthPipeDExact r e u v j‖
      ≤ (3 * (∑ i, (e i : ℝ)) + 2) / 2 ^ p := by
    rw [le_div_iff₀ hp, mul_comm]
    exact h
  gcongr

end Pipeline

end IntegerMultBounds.NLogN
