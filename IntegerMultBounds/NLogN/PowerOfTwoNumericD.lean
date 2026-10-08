import IntegerMultBounds.NLogN.PowerOfTwoExactD
import IntegerMultBounds.NLogN.SynthConvApproxD
import IntegerMultBounds.NLogN.PowerOfTwoNumeric

/-! Theorem 3.1 of Harvey and van der Hoeven for `d + 1` power-of-two
coordinates. The numerical transform rounds the chirp pre-multiplication,
splits off the last coordinate, twists, runs the `d`-dimensional synthetic
pipeline with numerical forward transforms and rounded `1/r`-scaled products,
untwists, scales by `T' = ∏_{i<d} t_i`, and rounds the chirp
post-multiplication. Proved: the normalized `d`-dimensional complex transform
is a contraction; the generic synthetic pipeline built from any numerical
transforms of scaled error `S` that preserve the unit ball has scaled error
`3 S + 2`; the exact pipeline is bilinear with error `δ₁ + δ₂` on unit balls;
and the full numerical transform has scaled error at most
`T' (3 S + 2 εa + 4) + εa + 2`, where `εa` is the scaled error of the
approximate chirp; with `εa ≤ 2` this is `3 T' S + 8 T' + 4`. The numerical
one-dimensional transforms are abstract here (Proposition 3.3 supplies them,
with `S = ∑ log₂ t_i`); per-term chirp evaluation and bit costs are not
modelled. -/

namespace IntegerMultBounds.NLogN

open Complex Real

section Contraction

variable {d : ℕ} {N : Fin d → ℕ} [∀ i, NeZero (N i)]

theorem norm_exp_neg_two_pi_div_pow (n m : ℕ) :
    ‖Complex.exp (-2 * π * I / (n : ℕ)) ^ m‖ = 1 := by
  rw [norm_pow]
  have : (-2 * π * I / (n : ℕ) : ℂ) = ((-2 * π / n : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I, one_pow]

/-- The normalized `d`-dimensional transform is a contraction. -/
theorem norm_dftNormD_le {u : ((i : Fin d) → ZMod (N i)) → ℂ} (hu : ∀ j, ‖u j‖ ≤ 1)
    (k : (i : Fin d) → ZMod (N i)) : ‖dftNormD N u k‖ ≤ 1 := by
  simp only [dftNormD, dftD]
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hT : (0 : ℝ) < ((∏ i, N i : ℕ) : ℝ) := by
    rw [Nat.cast_pos]
    exact Finset.prod_pos fun i _ => NeZero.pos (N i)
  have hsum : ‖∑ j, (∏ i, Complex.exp (-2 * π * I / (N i)) ^ (j i * k i).val) * u j‖
      ≤ ((∏ i, N i : ℕ) : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ j : (i : Fin d) → ZMod (N i),
        ‖(∏ i, Complex.exp (-2 * π * I / (N i)) ^ (j i * k i).val) * u j‖ ≤ 1 := by
      intro j
      rw [norm_mul, norm_prod]
      simp only [norm_exp_neg_two_pi_div_pow, Finset.prod_const_one, one_mul]
      exact hu j
    refine (Finset.sum_le_card_nsmul _ _ _ (fun j _ => hterm j)).trans ?_
    rw [Finset.card_univ, card_pi_zmod]
    simp
  calc 1 / ((∏ i, N i : ℕ) : ℝ) * ‖_‖ ≤ 1 / ((∏ i, N i : ℕ) : ℝ) * ((∏ i, N i : ℕ) : ℝ) := by
        gcongr
    _ = 1 := by field_simp

end Contraction

section PreMul

/-- The rounded chirp pre-multiplication `b̃ = round(ā · u)` on any index type. -/
noncomputable def preMulD (p : ℕ) {ι : Type*} (a' u : ι → ℂ) : ι → ℂ :=
  fun j => rhoC p ((starRingEnd ℂ) (a' j) * u j)

variable {d : ℕ} {N : Fin d → ℕ} [∀ i, NeZero (N i)]

omit [∀ i, NeZero (N i)] in
theorem preMulD_err {p : ℕ} {εa : ℝ} {a' u : ((i : Fin d) → ZMod (N i)) → ℂ}
    (ha : ∀ j, 2 ^ p * ‖a' j - chirpD N j‖ ≤ εa) (ha1 : ∀ j, ‖a' j‖ ≤ 1)
    (hu : ∀ j, ‖u j‖ ≤ 1) (j : (i : Fin d) → ZMod (N i)) :
    2 ^ p * ‖preMulD p a' u j - (starRingEnd ℂ) (chirpD N j) * u j‖ ≤ εa + 2 := by
  have h := approx_mul_round (p := p) (η₁ := εa) (η₂ := 0)
    (u' := (starRingEnd ℂ) (a' j)) (v' := u j) (u := (starRingEnd ℂ) (chirpD N j)) (v := u j)
    (by rw [Complex.norm_conj]; exact ha1 j) (hu j)
    (by rw [Complex.norm_conj, norm_chirpD])
    (by rw [← map_sub, Complex.norm_conj]; exact ha j)
    (by simp)
  simp only [preMulD]
  linarith

omit [∀ i, NeZero (N i)] in
theorem norm_preMulD_le {p : ℕ} {ι : Type*} {a' u : ι → ℂ} (ha1 : ∀ j, ‖a' j‖ ≤ 1)
    (hu : ∀ j, ‖u j‖ ≤ 1) (j : ι) : ‖preMulD p a' u j‖ ≤ 1 := by
  simp only [preMulD]
  refine (norm_rhoC_le p _).trans ?_
  rw [norm_mul, Complex.norm_conj]
  calc ‖a' j‖ * ‖u j‖ ≤ 1 * 1 := by gcongr; exact ha1 j; exact hu j
    _ = 1 := one_mul 1

end PreMul

section Transport

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Precomposition with any map is contractive in the sup norm. -/
theorem norm_comp_le (f : ι → κ) (x : κ → ℂ) : ‖x ∘ f‖ ≤ ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  exact norm_le_pi_norm x (f i)

omit [Fintype ι] [Fintype κ] in
theorem comp_sub_apply (f : ι → κ) (x y : κ → ℂ) : (x ∘ f) - (y ∘ f) = (x - y) ∘ f := rfl

theorem norm_comp_sub_le (f : ι → κ) (x y : κ → ℂ) : ‖x ∘ f - y ∘ f‖ ≤ ‖x - y‖ := by
  rw [comp_sub_apply]
  exact norm_comp_le f (x - y)

end Transport

section GenericPipeline

variable {r : ℕ} [NeZero r] {d : ℕ}

/-- The exact normalised `d`-dimensional synthetic pipeline before the final scaling,
for arbitrary positive lengths. -/
noncomputable def synthPipeGenExact (r : ℕ) [NeZero r] (N : Fin d → ℕ)
    (u v : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ) :=
  synthDFTDInv r N fun j =>
    (1 / (r : ℂ)) • negacyclicMul (synthDFTD r N u j) (synthDFTD r N v j)

/-- The numerical pipeline built from arbitrary numerical forward transforms
`F₁' F₂' F₃'`: numerical forward transforms, rounded `1/r`-scaled products, and the
numerical inverse transform taken as the forward one at the negated index. -/
noncomputable def synthPipeGen (r : ℕ) [NeZero r] (N : Fin d → ℕ) [∀ i, NeZero (N i)] (p : ℕ)
    (F₁' F₂' F₃' : (((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) →
      (((i : Fin d) → Fin (N i)) → (Fin r → ℂ)))
    (u v : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ) :=
  fun j => F₃' (fun j => rdC p ((1 / (r : ℂ)) • negacyclicMul (F₁' u j) (F₂' v j))) (-j)

variable {N : Fin d → ℕ} [∀ i, NeZero (N i)]

/-- The exact pipeline is bilinear and contractive: perturbing the inputs by `δ₁`, `δ₂`
on unit balls perturbs the output by at most `δ₁ + δ₂`. -/
theorem synthPipeGenExact_bilinear_err
    {x x' y y' : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)} {δ₁ δ₂ : ℝ}
    (hx : ∀ j, ‖x j‖ ≤ 1) (hy' : ∀ j, ‖y' j‖ ≤ 1)
    (hx' : ∀ j, ‖x' j - x j‖ ≤ δ₁) (hy : ∀ j, ‖y' j - y j‖ ≤ δ₂)
    (j : (i : Fin d) → Fin (N i)) :
    ‖synthPipeGenExact r N x' y' j - synthPipeGenExact r N x y j‖ ≤ δ₁ + δ₂ := by
  simp only [synthPipeGenExact, synthDFTDInv_eq]
  rw [synthDFTD_sub_apply]
  refine norm_synthDFTD_le (A := δ₁ + δ₂) (fun i => ?_) (-j)
  have hFx : ∀ i, ‖synthDFTD r N x' i - synthDFTD r N x i‖ ≤ δ₁ := fun i => by
    rw [synthDFTD_sub_apply]; exact norm_synthDFTD_le hx' i
  have hFy : ∀ i, ‖synthDFTD r N y' i - synthDFTD r N y i‖ ≤ δ₂ := fun i => by
    rw [synthDFTD_sub_apply]; exact norm_synthDFTD_le hy i
  exact normProd_err' (norm_synthDFTD_le hx i) (norm_synthDFTD_le hy' i) (hFx i) (hFy i)

/-- Proposition 3.4 in generic form: numerical forward transforms of elementwise error
`δ` preserving the unit ball give a pipeline error of `3 δ + 2 / 2^p`. -/
theorem synthPipeGen_err {p : ℕ} {δ : ℝ}
    {F₁' F₂' F₃' : (((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) →
      (((i : Fin d) → Fin (N i)) → (Fin r → ℂ))}
    (hF₁ : ∀ w, ‖w‖ ≤ 1 → ∀ k, ‖F₁' w k - synthDFTD r N w k‖ ≤ δ)
    (hF₂ : ∀ w, ‖w‖ ≤ 1 → ∀ k, ‖F₂' w k - synthDFTD r N w k‖ ≤ δ)
    (hF₃ : ∀ w, ‖w‖ ≤ 1 → ∀ k, ‖F₃' w k - synthDFTD r N w k‖ ≤ δ)
    (hF₁ball : ∀ w, ‖w‖ ≤ 1 → ‖F₁' w‖ ≤ 1) (hF₂ball : ∀ w, ‖w‖ ≤ 1 → ‖F₂' w‖ ≤ 1)
    {u v : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (j : (i : Fin d) → Fin (N i)) :
    ‖synthPipeGen r N p F₁' F₂' F₃' u v j - synthPipeGenExact r N u v j‖
      ≤ 3 * δ + 2 / 2 ^ p := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set Fu' := F₁' u
  set Fv' := F₂' v
  set Fu := synthDFTD r N u
  set Fv := synthDFTD r N v
  set z' : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ) :=
    fun j => rdC p ((1 / (r : ℂ)) • negacyclicMul (Fu' j) (Fv' j))
  set z : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ) :=
    fun j => (1 / (r : ℂ)) • negacyclicMul (Fu j) (Fv j)
  have hFu : ∀ k, ‖Fu' k - Fu k‖ ≤ δ := hF₁ u hu
  have hFv : ∀ k, ‖Fv' k - Fv k‖ ≤ δ := hF₂ v hv
  have hFu1 : ∀ k, ‖Fu k‖ ≤ 1 := fun k =>
    norm_synthDFTD_le (fun j => (norm_le_pi_norm u j).trans hu) k
  have hFv'1 : ∀ k, ‖Fv' k‖ ≤ 1 := fun k => (norm_le_pi_norm _ k).trans (hF₂ball v hv)
  have hFu'1 : ∀ k, ‖Fu' k‖ ≤ 1 := fun k => (norm_le_pi_norm _ k).trans (hF₁ball u hu)
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
  have hexact : synthPipeGenExact r N u v j = synthDFTD r N z (-j) := rfl
  have happrox : synthPipeGen r N p F₁' F₂' F₃' u v j = F₃' z' (-j) := rfl
  rw [hexact, happrox]
  have hsub : ∀ k, ‖synthDFTD r N z' k - synthDFTD r N z k‖ ≤ 2 / 2 ^ p + 2 * δ := by
    intro k
    rw [synthDFTD_sub_apply]
    exact norm_synthDFTD_le hz k
  calc ‖F₃' z' (-j) - synthDFTD r N z (-j)‖
      = ‖(F₃' z' (-j) - synthDFTD r N z' (-j)) + (synthDFTD r N z' (-j) - synthDFTD r N z (-j))‖ := by
        congr 1; abel
    _ ≤ ‖F₃' z' (-j) - synthDFTD r N z' (-j)‖ + ‖synthDFTD r N z' (-j) - synthDFTD r N z (-j)‖ :=
        norm_add_le _ _
    _ ≤ δ + (2 / 2 ^ p + 2 * δ) := add_le_add (hF₃ z' hz'1 (-j)) (hsub (-j))
    _ = 3 * δ + 2 / 2 ^ p := by ring

end GenericPipeline

section Numeric

variable {d : ℕ}

/-- The numerical `(d+1)`-coordinate transform: chirp, split, twist, generic synthetic
pipeline, untwist, scale by `T'`, chirp, with rounding at both chirp multiplications. -/
noncomputable def transformDNum (M : Fin (d + 1) → ℕ) (p : ℕ)
    (F₁' F₂' F₃' : (((i : Fin d) → Fin (lenInit M i)) → (Fin (lenLast M) → ℂ)) →
      (((i : Fin d) → Fin (lenInit M i)) → (Fin (lenLast M) → ℂ)))
    (a' u : ((i : Fin (d + 1)) → ZMod (M i + 1)) → ℂ) :
    ((i : Fin (d + 1)) → ZMod (M i + 1)) → ℂ :=
  fun k => rhoC p ((starRingEnd ℂ) (a' k) * ofSynth (fun j => ((∏ i, lenInit M i : ℕ) : ℂ) •
    synthPipeGen (lenLast M) (lenInit M) p F₁' F₂' F₃'
      (toSynth (a' ∘ (splitLast M).symm))
      (toSynth (preMulD p a' u ∘ (splitLast M).symm)) j) (splitLast M k))

/-- Theorem 3.1 for `d + 1` power-of-two coordinates: with numerical forward transforms
of scaled error `S` preserving the unit ball and an approximate chirp of scaled error
`εa`, the numerical transform has scaled error `T' (3 S + 2 εa + 4) + εa + 2`. -/
theorem transformD_err (M : Fin (d + 1) → ℕ) {p : ℕ} {S εa : ℝ}
    (hpow : ∀ i, ∃ f, M i + 1 = 2 ^ f) (heven : ∀ i, 2 ∣ M i + 1)
    (hdiv : ∀ i : Fin d, M (Fin.castSucc i) + 1 ∣ 2 * (M (Fin.last d) + 1))
    {F₁' F₂' F₃' : (((i : Fin d) → Fin (lenInit M i)) → (Fin (lenLast M) → ℂ)) →
      (((i : Fin d) → Fin (lenInit M i)) → (Fin (lenLast M) → ℂ))}
    (hF₁ : ∀ w, ‖w‖ ≤ 1 → ∀ k, 2 ^ p * ‖F₁' w k - synthDFTD (lenLast M) (lenInit M) w k‖ ≤ S)
    (hF₂ : ∀ w, ‖w‖ ≤ 1 → ∀ k, 2 ^ p * ‖F₂' w k - synthDFTD (lenLast M) (lenInit M) w k‖ ≤ S)
    (hF₃ : ∀ w, ‖w‖ ≤ 1 → ∀ k, 2 ^ p * ‖F₃' w k - synthDFTD (lenLast M) (lenInit M) w k‖ ≤ S)
    (hF₁ball : ∀ w, ‖w‖ ≤ 1 → ‖F₁' w‖ ≤ 1) (hF₂ball : ∀ w, ‖w‖ ≤ 1 → ‖F₂' w‖ ≤ 1)
    {a' u : ((i : Fin (d + 1)) → ZMod (M i + 1)) → ℂ}
    (ha : ∀ j, 2 ^ p * ‖a' j - chirpD (lenAll M) j‖ ≤ εa) (ha1 : ∀ j, ‖a' j‖ ≤ 1)
    (hu : ∀ j, ‖u j‖ ≤ 1) (k : (i : Fin (d + 1)) → ZMod (M i + 1)) :
    2 ^ p * ‖transformDNum M p F₁' F₂' F₃' a' u k - dftNormD (lenAll M) u k‖
      ≤ ((∏ i, lenInit M i : ℕ) : ℝ) * (3 * S + 2 * εa + 4) + εa + 2 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hεa : 0 ≤ εa := le_trans (by positivity) (ha k)
  have hS : 0 ≤ S := by
    have := hF₁ (fun _ => 0) (by simp) (fun _ => 0)
    exact le_trans (by positivity) this
  set T' : ℝ := ((∏ i, lenInit M i : ℕ) : ℝ) with hT'
  have hT'0 : 0 ≤ T' := by positivity
  -- names
  set a : ((i : Fin (d + 1)) → ZMod (M i + 1)) → ℂ := chirpD (lenAll M) with ha_def
  set b : ((i : Fin (d + 1)) → ZMod (M i + 1)) → ℂ := fun j => (starRingEnd ℂ) (a j) * u j
    with hb_def
  set b' : ((i : Fin (d + 1)) → ZMod (M i + 1)) → ℂ := preMulD p a' u with hb'_def
  set sa := a ∘ (splitLast M).symm
  set sa' := a' ∘ (splitLast M).symm
  set sb := b ∘ (splitLast M).symm
  set sb' := b' ∘ (splitLast M).symm
  set inner : ((i : Fin d) → Fin (lenInit M i)) → (Fin (lenLast M) → ℂ) :=
    fun j => ((∏ i, lenInit M i : ℕ) : ℂ) • synthPipeGenExact (lenLast M) (lenInit M) (toSynth sa) (toSynth sb) j
    with hinner
  set inner' : ((i : Fin d) → Fin (lenInit M i)) → (Fin (lenLast M) → ℂ) :=
    fun j => ((∏ i, lenInit M i : ℕ) : ℂ) •
      synthPipeGen (lenLast M) (lenInit M) p F₁' F₂' F₃' (toSynth sa') (toSynth sb') j with hinner'
  -- the exact value through the chain
  have hchain : dftNormD (lenAll M) u k = (starRingEnd ℂ) (a k) * ofSynth inner (splitLast M k) := by
    have := congrFun (dftNormD_chain M hpow heven hdiv u) k
    exact this
  -- step 1: pre-multiplication
  have hb'err : ∀ j, ‖b' j - b j‖ ≤ (εa + 2) / 2 ^ p := fun j => by
    rw [le_div_iff₀ hp, mul_comm]; exact preMulD_err ha ha1 hu j
  have hb'1 : ∀ j, ‖b' j‖ ≤ 1 := fun j => norm_preMulD_le ha1 hu j
  have hb'sup : ‖b' - b‖ ≤ (εa + 2) / 2 ^ p := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j; exact hb'err j
  have ha'sup : ‖a' - a‖ ≤ εa / 2 ^ p := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    rw [le_div_iff₀ hp, mul_comm]; exact ha j
  have ha1sup : ‖a‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]; intro i; exact (norm_chirpD i).le
  have ha'1sup : ‖a'‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]; exact ha1
  have hb'1sup : ‖b'‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]; exact hb'1
  -- step 2: split and twist
  have hta : ∀ j, ‖toSynth sa j‖ ≤ 1 := fun j =>
    (norm_toSynth_le sa j).trans ((norm_comp_le _ a).trans ha1sup)
  have hta' : ∀ j, ‖toSynth sa' j‖ ≤ 1 := fun j =>
    (norm_toSynth_le sa' j).trans ((norm_comp_le _ a').trans ha'1sup)
  have htb' : ∀ j, ‖toSynth sb' j‖ ≤ 1 := fun j =>
    (norm_toSynth_le sb' j).trans ((norm_comp_le _ b').trans hb'1sup)
  have hta'err : ∀ j, ‖toSynth sa' j - toSynth sa j‖ ≤ εa / 2 ^ p := fun j =>
    (norm_toSynth_sub_le sa' sa j).trans ((norm_comp_sub_le _ a' a).trans ha'sup)
  have htb'err : ∀ j, ‖toSynth sb' j - toSynth sb j‖ ≤ (εa + 2) / 2 ^ p := fun j =>
    (norm_toSynth_sub_le sb' sb j).trans ((norm_comp_sub_le _ b' b).trans hb'sup)
  have hta'sup : ‖toSynth sa'‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]; exact hta'
  have htb'sup : ‖toSynth sb'‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]; exact htb'
  -- step 3: pipeline
  have hF₁' : ∀ w, ‖w‖ ≤ 1 → ∀ k, ‖F₁' w k - synthDFTD (lenLast M) (lenInit M) w k‖ ≤ S / 2 ^ p := by
    intro w hw k; rw [le_div_iff₀ hp, mul_comm]; exact hF₁ w hw k
  have hF₂' : ∀ w, ‖w‖ ≤ 1 → ∀ k, ‖F₂' w k - synthDFTD (lenLast M) (lenInit M) w k‖ ≤ S / 2 ^ p := by
    intro w hw k; rw [le_div_iff₀ hp, mul_comm]; exact hF₂ w hw k
  have hF₃' : ∀ w, ‖w‖ ≤ 1 → ∀ k, ‖F₃' w k - synthDFTD (lenLast M) (lenInit M) w k‖ ≤ S / 2 ^ p := by
    intro w hw k; rw [le_div_iff₀ hp, mul_comm]; exact hF₃ w hw k
  have hpipe : ∀ j, ‖synthPipeGen (lenLast M) (lenInit M) p F₁' F₂' F₃' (toSynth sa') (toSynth sb') j
      - synthPipeGenExact (lenLast M) (lenInit M) (toSynth sa) (toSynth sb) j‖ ≤ (3 * S + 2 * εa + 4) / 2 ^ p := by
    intro j
    have h1 := synthPipeGen_err (p := p) hF₁' hF₂' hF₃' hF₁ball hF₂ball hta'sup htb'sup j
    have h2 := synthPipeGenExact_bilinear_err (r := lenLast M) hta htb' hta'err htb'err j
    calc ‖synthPipeGen (lenLast M) (lenInit M) p F₁' F₂' F₃' (toSynth sa') (toSynth sb') j
          - synthPipeGenExact (lenLast M) (lenInit M) (toSynth sa) (toSynth sb) j‖
        = ‖(synthPipeGen (lenLast M) (lenInit M) p F₁' F₂' F₃' (toSynth sa') (toSynth sb') j
            - synthPipeGenExact (lenLast M) (lenInit M) (toSynth sa') (toSynth sb') j)
          + (synthPipeGenExact (lenLast M) (lenInit M) (toSynth sa') (toSynth sb') j
            - synthPipeGenExact (lenLast M) (lenInit M) (toSynth sa) (toSynth sb) j)‖ := by congr 1; abel
      _ ≤ ‖synthPipeGen (lenLast M) (lenInit M) p F₁' F₂' F₃' (toSynth sa') (toSynth sb') j
            - synthPipeGenExact (lenLast M) (lenInit M) (toSynth sa') (toSynth sb') j‖
          + ‖synthPipeGenExact (lenLast M) (lenInit M) (toSynth sa') (toSynth sb') j
            - synthPipeGenExact (lenLast M) (lenInit M) (toSynth sa) (toSynth sb) j‖ := norm_add_le _ _
      _ ≤ (3 * (S / 2 ^ p) + 2 / 2 ^ p) + (εa / 2 ^ p + (εa + 2) / 2 ^ p) := add_le_add h1 h2
      _ = (3 * S + 2 * εa + 4) / 2 ^ p := by ring
  -- the inner values after untwisting
  have hinnerErr : ∀ j, ‖inner' j - inner j‖ ≤ T' * ((3 * S + 2 * εa + 4) / 2 ^ p) := fun j => by
    have : inner' j - inner j = ((∏ i, lenInit M i : ℕ) : ℂ) •
        (synthPipeGen (lenLast M) (lenInit M) p F₁' F₂' F₃' (toSynth sa') (toSynth sb') j
          - synthPipeGenExact (lenLast M) (lenInit M) (toSynth sa) (toSynth sb) j) := by
      rw [smul_sub]
    rw [this, norm_smul, Complex.norm_natCast]
    gcongr
    exact hpipe j
  have hW : ‖ofSynth inner' (splitLast M k) - ofSynth inner (splitLast M k)‖
      ≤ T' * ((3 * S + 2 * εa + 4) / 2 ^ p) := by
    rw [ofSynth_sub]
    exact (norm_ofSynth_apply_le _ _).trans (hinnerErr _)
  have hWexact : ‖ofSynth inner (splitLast M k)‖ ≤ 1 := by
    have h := norm_dftNormD_le hu k
    rw [hchain, norm_mul, Complex.norm_conj, norm_chirpD, one_mul] at h
    exact h
  -- step 4: post-multiplication with rounding
  have hx' : ‖(starRingEnd ℂ) (a' k)‖ ≤ 1 := by rw [Complex.norm_conj]; exact ha1 k
  have hxx : ‖(starRingEnd ℂ) (a' k) - (starRingEnd ℂ) (a k)‖ ≤ εa / 2 ^ p := by
    rw [← map_sub, Complex.norm_conj, le_div_iff₀ hp, mul_comm]; exact ha k
  have hfinal : ‖transformDNum M p F₁' F₂' F₃' a' u k - dftNormD (lenAll M) u k‖
      ≤ 2 / 2 ^ p + T' * ((3 * S + 2 * εa + 4) / 2 ^ p) + εa / 2 ^ p := by
    rw [hchain]
    have e : rhoC p ((starRingEnd ℂ) (a' k) * ofSynth inner' (splitLast M k))
        - (starRingEnd ℂ) (a k) * ofSynth inner (splitLast M k)
        = (rhoC p ((starRingEnd ℂ) (a' k) * ofSynth inner' (splitLast M k))
            - (starRingEnd ℂ) (a' k) * ofSynth inner' (splitLast M k))
          + (starRingEnd ℂ) (a' k) * (ofSynth inner' (splitLast M k) - ofSynth inner (splitLast M k))
          + ((starRingEnd ℂ) (a' k) - (starRingEnd ℂ) (a k)) * ofSynth inner (splitLast M k) := by
      ring
    show ‖rhoC p ((starRingEnd ℂ) (a' k) * ofSynth inner' (splitLast M k))
        - (starRingEnd ℂ) (a k) * ofSynth inner (splitLast M k)‖ ≤ _
    rw [e]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_mul, norm_mul]
    have h1 := norm_rhoC_sub_le_two p ((starRingEnd ℂ) (a' k) * ofSynth inner' (splitLast M k))
    calc ‖rhoC p ((starRingEnd ℂ) (a' k) * ofSynth inner' (splitLast M k))
            - (starRingEnd ℂ) (a' k) * ofSynth inner' (splitLast M k)‖
          + ‖(starRingEnd ℂ) (a' k)‖ * ‖ofSynth inner' (splitLast M k) - ofSynth inner (splitLast M k)‖
          + ‖(starRingEnd ℂ) (a' k) - (starRingEnd ℂ) (a k)‖ * ‖ofSynth inner (splitLast M k)‖
        ≤ 2 / 2 ^ p + 1 * (T' * ((3 * S + 2 * εa + 4) / 2 ^ p)) + εa / 2 ^ p * 1 := by
          gcongr
      _ = 2 / 2 ^ p + T' * ((3 * S + 2 * εa + 4) / 2 ^ p) + εa / 2 ^ p := by ring
  calc 2 ^ p * ‖transformDNum M p F₁' F₂' F₃' a' u k - dftNormD (lenAll M) u k‖
      ≤ 2 ^ p * (2 / 2 ^ p + T' * ((3 * S + 2 * εa + 4) / 2 ^ p) + εa / 2 ^ p) := by
        gcongr
    _ = T' * (3 * S + 2 * εa + 4) + εa + 2 := by
        field_simp; ring

/-- With chirp error `εa ≤ 2`: scaled error at most `3 T' S + 8 T' + 4`. -/
theorem transformD_err_simple (M : Fin (d + 1) → ℕ) {p : ℕ} {S εa : ℝ}
    (hpow : ∀ i, ∃ f, M i + 1 = 2 ^ f) (heven : ∀ i, 2 ∣ M i + 1)
    (hdiv : ∀ i : Fin d, M (Fin.castSucc i) + 1 ∣ 2 * (M (Fin.last d) + 1))
    {F₁' F₂' F₃' : (((i : Fin d) → Fin (lenInit M i)) → (Fin (lenLast M) → ℂ)) →
      (((i : Fin d) → Fin (lenInit M i)) → (Fin (lenLast M) → ℂ))}
    (hF₁ : ∀ w, ‖w‖ ≤ 1 → ∀ k, 2 ^ p * ‖F₁' w k - synthDFTD (lenLast M) (lenInit M) w k‖ ≤ S)
    (hF₂ : ∀ w, ‖w‖ ≤ 1 → ∀ k, 2 ^ p * ‖F₂' w k - synthDFTD (lenLast M) (lenInit M) w k‖ ≤ S)
    (hF₃ : ∀ w, ‖w‖ ≤ 1 → ∀ k, 2 ^ p * ‖F₃' w k - synthDFTD (lenLast M) (lenInit M) w k‖ ≤ S)
    (hF₁ball : ∀ w, ‖w‖ ≤ 1 → ‖F₁' w‖ ≤ 1) (hF₂ball : ∀ w, ‖w‖ ≤ 1 → ‖F₂' w‖ ≤ 1)
    {a' u : ((i : Fin (d + 1)) → ZMod (M i + 1)) → ℂ}
    (ha : ∀ j, 2 ^ p * ‖a' j - chirpD (lenAll M) j‖ ≤ εa) (hεa : εa ≤ 2) (ha1 : ∀ j, ‖a' j‖ ≤ 1)
    (hu : ∀ j, ‖u j‖ ≤ 1) (k : (i : Fin (d + 1)) → ZMod (M i + 1)) :
    2 ^ p * ‖transformDNum M p F₁' F₂' F₃' a' u k - dftNormD (lenAll M) u k‖
      ≤ 3 * ((∏ i, lenInit M i : ℕ) : ℝ) * S + 8 * ((∏ i, lenInit M i : ℕ) : ℝ) + 4 := by
  have h := transformD_err M hpow heven hdiv hF₁ hF₂ hF₃ hF₁ball hF₂ball ha ha1 hu k
  have hT' : (0 : ℝ) ≤ ((∏ i, lenInit M i : ℕ) : ℝ) := by positivity
  calc 2 ^ p * ‖transformDNum M p F₁' F₂' F₃' a' u k - dftNormD (lenAll M) u k‖
      ≤ ((∏ i, lenInit M i : ℕ) : ℝ) * (3 * S + 2 * εa + 4) + εa + 2 := h
    _ ≤ ((∏ i, lenInit M i : ℕ) : ℝ) * (3 * S + 2 * 2 + 4) + 2 + 2 := by gcongr
    _ = 3 * ((∏ i, lenInit M i : ℕ) : ℝ) * S + 8 * ((∏ i, lenInit M i : ℕ) : ℝ) + 4 := by ring

end Numeric

end IntegerMultBounds.NLogN
