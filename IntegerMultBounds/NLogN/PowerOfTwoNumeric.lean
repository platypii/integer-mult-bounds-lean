import IntegerMultBounds.NLogN.PowerOfTwoExact
import IntegerMultBounds.NLogN.SynthConvApprox

/-! Theorem 3.1 of Harvey and van der Hoeven for two power-of-two coordinates
`t × r` with `t = 2^n`: the numerical transform that rounds the chirp
pre-multiplication, runs the synthetic pipeline with per-level error oracles
and rounded products on the twisted slices, untwists, scales by `t`, and
rounds the chirp post-multiplication, approximates the normalized complex
transform with scaled error at most `t (4n + 2εa + 4) + εa + 2`, where `εa` is
the scaled error of the approximate chirp; with `εa ≤ 2` this is
`4 t n + 8 t + 4`. Proved along the way: the normalized transform is a
contraction, the twist is linear and contractive on slices, and the exact
synthetic pipeline is bilinear with error `δ₁ + δ₂` on unit-ball inputs. The
per-term evaluation of the chirp and the clamping conventions of the paper are
hypotheses; bit costs are not modelled. -/

namespace IntegerMultBounds.NLogN

open Complex Real

section Contraction

variable {t r : ℕ} [NeZero t] [NeZero r]

omit [NeZero t] [NeZero r] in
theorem norm_exp_neg_two_pi_div (m n : ℕ) :
    ‖Complex.exp (-2 * π * I * (m : ℕ) / n)‖ = 1 := by
  have : (-2 * π * I * (m : ℕ) / n : ℂ) = ((-2 * π * m / n : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- The normalized two-coordinate transform is a contraction. -/
theorem norm_dftNorm2_le {u : Fin t × Fin r → ℂ} (hu : ∀ j, ‖u j‖ ≤ 1) (k : Fin t × Fin r) :
    ‖dftNorm2 t r u k‖ ≤ 1 := by
  simp only [dftNorm2]
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have htr : (0 : ℝ) < ((t * r : ℕ) : ℝ) := by
    have := NeZero.pos t; have := NeZero.pos r; positivity
  have hsum : ‖∑ j : Fin t × Fin r, Complex.exp (-2 * π * I * (j.1.val * k.1.val : ℕ) / t) *
      Complex.exp (-2 * π * I * (j.2.val * k.2.val : ℕ) / r) * u j‖ ≤ ((t * r : ℕ) : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ j : Fin t × Fin r, ‖Complex.exp (-2 * π * I * (j.1.val * k.1.val : ℕ) / t) *
        Complex.exp (-2 * π * I * (j.2.val * k.2.val : ℕ) / r) * u j‖ ≤ 1 := by
      intro j
      rw [norm_mul, norm_mul, norm_exp_neg_two_pi_div, norm_exp_neg_two_pi_div, one_mul, one_mul]
      exact hu j
    refine (Finset.sum_le_card_nsmul _ _ _ (fun j _ => hterm j)).trans ?_
    simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  calc 1 / ((t * r : ℕ) : ℝ) * ‖_‖ ≤ 1 / ((t * r : ℕ) : ℝ) * ((t * r : ℕ) : ℝ) := by gcongr
    _ = 1 := by field_simp

end Contraction

section TwistLinear

variable {r : ℕ} [NeZero r] {G : Type*} [AddCommGroup G] [Fintype G]

omit [NeZero r] [AddCommGroup G] [Fintype G] in
theorem toSynth_sub (u v : G × Fin r → ℂ) (j : G) :
    toSynth u j - toSynth v j = toSynth (fun p => u p - v p) j := by
  funext k
  simp only [toSynth, twist, Pi.sub_apply]
  ring

omit [NeZero r] [AddCommGroup G] [Fintype G] in
theorem ofSynth_sub (w w' : G → (Fin r → ℂ)) (p : G × Fin r) :
    ofSynth w p - ofSynth w' p = ofSynth (fun j => w j - w' j) p := by
  simp only [ofSynth, untwist, Pi.sub_apply]
  ring

omit [NeZero r] [AddCommGroup G] [Fintype G] in
theorem norm_ofSynth_apply_le (w : G → (Fin r → ℂ)) (p : G × Fin r) :
    ‖ofSynth w p‖ ≤ ‖w p.1‖ := by
  simp only [ofSynth]
  rw [norm_untwist_apply]
  exact norm_le_pi_norm (w p.1) p.2

omit [NeZero r] [AddCommGroup G] in
/-- Slices of the twist are controlled by the sup norm of the difference. -/
theorem norm_toSynth_sub_le (u v : G × Fin r → ℂ) (j : G) :
    ‖toSynth u j - toSynth v j‖ ≤ ‖u - v‖ := by
  rw [toSynth_sub]
  exact norm_toSynth_le (fun p => u p - v p) j

end TwistLinear

section PipelineBilinear

variable {r : ℕ} [NeZero r]

/-- The normalized pointwise product error without the cross term, using a
unit bound on the second approximate factor. -/
theorem normProd_err' {a a' b b' : Fin r → ℂ} {δ₁ δ₂ : ℝ} (ha : ‖a‖ ≤ 1) (hb' : ‖b'‖ ≤ 1)
    (ha' : ‖a' - a‖ ≤ δ₁) (hb : ‖b' - b‖ ≤ δ₂) :
    ‖(1 / (r : ℂ)) • negacyclicMul a' b' - (1 / (r : ℂ)) • negacyclicMul a b‖ ≤ δ₁ + δ₂ := by
  have hδ₁ : 0 ≤ δ₁ := (norm_nonneg _).trans ha'
  have hδ₂ : 0 ≤ δ₂ := (norm_nonneg _).trans hb
  have hsplit : negacyclicMul a' b' - negacyclicMul a b
      = negacyclicMul (a' - a) b' + negacyclicMul a (b' - b) := by
    rw [negacyclicMul_sub_left, negacyclicMul_sub_right]; abel
  rw [← smul_sub, hsplit, smul_add]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_normProd_le (a' - a) b'
  have h2 := norm_normProd_le a (b' - b)
  calc ‖(1 / (r : ℂ)) • negacyclicMul (a' - a) b'‖ + ‖(1 / (r : ℂ)) • negacyclicMul a (b' - b)‖
      ≤ ‖a' - a‖ * ‖b'‖ + ‖a‖ * ‖b' - b‖ := add_le_add h1 h2
    _ ≤ δ₁ * 1 + 1 * δ₂ := by gcongr
    _ = δ₁ + δ₂ := by ring

/-- The exact synthetic pipeline is bilinear and contractive: perturbing the two
inputs by `δ₁`, `δ₂` on unit balls perturbs the output by at most `δ₁ + δ₂`. -/
theorem synthPipeExact_bilinear_err {n : ℕ} (hr : 2 ^ n ∣ 2 * r)
    {x x' y y' : Fin (2 ^ n) → (Fin r → ℂ)} {δ₁ δ₂ : ℝ}
    (hx : ∀ j, ‖x j‖ ≤ 1) (hy' : ∀ j, ‖y' j‖ ≤ 1)
    (hx' : ∀ j, ‖x' j - x j‖ ≤ δ₁) (hy : ∀ j, ‖y' j - y j‖ ≤ δ₂) (j : Fin (2 ^ n)) :
    ‖synthPipeExact n x' y' j - synthPipeExact n x y j‖ ≤ δ₁ + δ₂ := by
  simp only [synthPipeExact]
  rw [synthDFTInv_sub]
  refine norm_synthDFTInv_le (A := δ₁ + δ₂) (fun i => ?_) j
  have hFx : ∀ i, ‖synthDFT r (2 ^ n) x' i - synthDFT r (2 ^ n) x i‖ ≤ δ₁ := fun i => by
    rw [synthDFT_sub hr]; exact norm_synthDFT_le hr hx' i
  have hFy : ∀ i, ‖synthDFT r (2 ^ n) y' i - synthDFT r (2 ^ n) y i‖ ≤ δ₂ := fun i => by
    rw [synthDFT_sub hr]; exact norm_synthDFT_le hr hy i
  exact normProd_err' (norm_synthDFT_le hr hx i) (norm_synthDFT_le hr hy' i) (hFx i) (hFy i)

end PipelineBilinear

section Numeric

variable {r : ℕ} [NeZero r]

/-- The rounded chirp pre-multiplication `b̃ = round(ā · u)`. -/
noncomputable def preMul2 (p : ℕ) {t : ℕ} (a' u : Fin t × Fin r → ℂ) : Fin t × Fin r → ℂ :=
  fun j => rhoC p ((starRingEnd ℂ) (a' j) * u j)

/-- The numerical two-coordinate transform: chirp, twist, synthetic pipeline,
untwist, scale by `t`, chirp, with rounding at both chirp multiplications. -/
noncomputable def transform2Num (n p : ℕ)
    (e₁ e₂ e₃ : (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ))
    (a' u : Fin (2 ^ n) × Fin r → ℂ) : Fin (2 ^ n) × Fin r → ℂ :=
  fun k => rhoC p ((starRingEnd ℂ) (a' k) * ofSynth (fun j => ((2 ^ n : ℕ) : ℂ) •
    synthPipeApprox n p e₁ e₂ e₃ (toSynth a') (toSynth (preMul2 p a' u)) j) k)

omit [NeZero r] in
theorem preMul2_err {p t : ℕ} {εa : ℝ} {a' u : Fin t × Fin r → ℂ}
    (ha : ∀ j, 2 ^ p * ‖a' j - chirp2 t r j‖ ≤ εa) (ha1 : ∀ j, ‖a' j‖ ≤ 1)
    (hu : ∀ j, ‖u j‖ ≤ 1) (j : Fin t × Fin r) :
    2 ^ p * ‖preMul2 p a' u j - (starRingEnd ℂ) (chirp2 t r j) * u j‖ ≤ εa + 2 := by
  have h := approx_mul_round (p := p) (η₁ := εa) (η₂ := 0)
    (u' := (starRingEnd ℂ) (a' j)) (v' := u j) (u := (starRingEnd ℂ) (chirp2 t r j)) (v := u j)
    (by rw [Complex.norm_conj]; exact ha1 j) (hu j)
    (by rw [Complex.norm_conj, norm_chirp2])
    (by rw [← map_sub, Complex.norm_conj]; exact ha j)
    (by simp)
  simp only [preMul2]
  linarith

omit [NeZero r] in
theorem norm_preMul2_le {p t : ℕ} {a' u : Fin t × Fin r → ℂ} (ha1 : ∀ j, ‖a' j‖ ≤ 1)
    (hu : ∀ j, ‖u j‖ ≤ 1) (j : Fin t × Fin r) : ‖preMul2 p a' u j‖ ≤ 1 := by
  simp only [preMul2]
  refine (norm_rhoC_le p _).trans ?_
  rw [norm_mul, Complex.norm_conj]
  calc ‖a' j‖ * ‖u j‖ ≤ 1 * 1 := by gcongr; exact ha1 j; exact hu j
    _ = 1 := one_mul 1

/-- Theorem 3.1 for two power-of-two coordinates: scaled error
`t (4n + 2εa + 4) + εa + 2`. -/
theorem transform2_err {n p : ℕ} {εa : ℝ} (ht2 : 2 ∣ 2 ^ n) (hr2 : 2 ∣ r)
    (htr : 2 ^ n ∣ 2 * r) (hn : (n : ℝ) ≤ 2 ^ p)
    {e₁ e₂ e₃ : (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)}
    (he₁ : ∀ m k, ‖e₁ m k‖ ≤ 1 / 2 ^ p) (he₂ : ∀ m k, ‖e₂ m k‖ ≤ 1 / 2 ^ p)
    (he₃ : ∀ m k, ‖e₃ m k‖ ≤ 1 / 2 ^ p)
    {a' u : Fin (2 ^ n) × Fin r → ℂ}
    (ha : ∀ j, 2 ^ p * ‖a' j - chirp2 (2 ^ n) r j‖ ≤ εa) (ha1 : ∀ j, ‖a' j‖ ≤ 1)
    (hu : ∀ j, ‖u j‖ ≤ 1) (k : Fin (2 ^ n) × Fin r) :
    2 ^ p * ‖transform2Num n p e₁ e₂ e₃ a' u k - dftNorm2 (2 ^ n) r u k‖
      ≤ (2 ^ n : ℝ) * (4 * n + 2 * εa + 4) + εa + 2 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hεa : 0 ≤ εa := le_trans (by positivity) (ha k)
  -- names
  set a : Fin (2 ^ n) × Fin r → ℂ := chirp2 (2 ^ n) r with ha_def
  set b : Fin (2 ^ n) × Fin r → ℂ := fun j => (starRingEnd ℂ) (a j) * u j with hb_def
  set b' : Fin (2 ^ n) × Fin r → ℂ := preMul2 p a' u with hb'_def
  set inner : Fin (2 ^ n) → (Fin r → ℂ) :=
    fun j => ((2 ^ n : ℕ) : ℂ) • synthPipeExact n (toSynth a) (toSynth b) j with hinner
  set inner' : Fin (2 ^ n) → (Fin r → ℂ) :=
    fun j => ((2 ^ n : ℕ) : ℂ) • synthPipeApprox n p e₁ e₂ e₃ (toSynth a') (toSynth b') j
    with hinner'
  -- the exact value through the chain
  have hchain : dftNorm2 (2 ^ n) r u k = (starRingEnd ℂ) (a k) * ofSynth inner k := by
    have := congrFun (dftNorm2_chain (f := n) ht2 hr2 htr rfl u) k
    exact this
  -- step 1: pre-multiplication
  have hb'err : ∀ j, ‖b' j - b j‖ ≤ (εa + 2) / 2 ^ p := fun j => by
    rw [le_div_iff₀ hp, mul_comm]; exact preMul2_err ha ha1 hu j
  have hb'1 : ∀ j, ‖b' j‖ ≤ 1 := fun j => norm_preMul2_le ha1 hu j
  have hb'sup : ‖b' - b‖ ≤ (εa + 2) / 2 ^ p := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j; exact hb'err j
  have ha'sup : ‖a' - a‖ ≤ εa / 2 ^ p := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    rw [le_div_iff₀ hp, mul_comm]; exact ha j
  -- step 2: twisted inputs
  have hta : ∀ j, ‖toSynth a j‖ ≤ 1 := fun j =>
    (norm_toSynth_le a j).trans (by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]; intro i; exact (norm_chirp2 i).le)
  have hta' : ∀ j, ‖toSynth a' j‖ ≤ 1 := fun j =>
    (norm_toSynth_le a' j).trans (by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]; exact ha1)
  have htb' : ∀ j, ‖toSynth b' j‖ ≤ 1 := fun j =>
    (norm_toSynth_le b' j).trans (by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]; exact hb'1)
  have hta'err : ∀ j, ‖toSynth a' j - toSynth a j‖ ≤ εa / 2 ^ p := fun j =>
    (norm_toSynth_sub_le a' a j).trans ha'sup
  have htb'err : ∀ j, ‖toSynth b' j - toSynth b j‖ ≤ (εa + 2) / 2 ^ p := fun j =>
    (norm_toSynth_sub_le b' b j).trans hb'sup
  -- step 3: pipeline
  have hpipe : ∀ j, ‖synthPipeApprox n p e₁ e₂ e₃ (toSynth a') (toSynth b') j
      - synthPipeExact n (toSynth a) (toSynth b) j‖ ≤ (4 * n + 2 * εa + 4) / 2 ^ p := by
    intro j
    have h1 := synthPipe_err_scaled htr hn he₁ he₂ he₃ hta' htb' j
    have h1' : ‖synthPipeApprox n p e₁ e₂ e₃ (toSynth a') (toSynth b') j
        - synthPipeExact n (toSynth a') (toSynth b') j‖ ≤ (4 * n + 2) / 2 ^ p := by
      rw [le_div_iff₀ hp, mul_comm]; exact h1
    have h2 := synthPipeExact_bilinear_err htr hta htb' hta'err htb'err j
    calc ‖synthPipeApprox n p e₁ e₂ e₃ (toSynth a') (toSynth b') j
          - synthPipeExact n (toSynth a) (toSynth b) j‖
        = ‖(synthPipeApprox n p e₁ e₂ e₃ (toSynth a') (toSynth b') j
            - synthPipeExact n (toSynth a') (toSynth b') j)
          + (synthPipeExact n (toSynth a') (toSynth b') j
            - synthPipeExact n (toSynth a) (toSynth b) j)‖ := by congr 1; abel
      _ ≤ ‖synthPipeApprox n p e₁ e₂ e₃ (toSynth a') (toSynth b') j
            - synthPipeExact n (toSynth a') (toSynth b') j‖
          + ‖synthPipeExact n (toSynth a') (toSynth b') j
            - synthPipeExact n (toSynth a) (toSynth b) j‖ := norm_add_le _ _
      _ ≤ (4 * n + 2) / 2 ^ p + (εa / 2 ^ p + (εa + 2) / 2 ^ p) := add_le_add h1' h2
      _ = (4 * n + 2 * εa + 4) / 2 ^ p := by ring
  -- the inner values after untwisting
  have hinnerErr : ∀ j, ‖inner' j - inner j‖
      ≤ (2 ^ n : ℝ) * ((4 * n + 2 * εa + 4) / 2 ^ p) := fun j => by
    have : inner' j - inner j = ((2 ^ n : ℕ) : ℂ) •
        (synthPipeApprox n p e₁ e₂ e₃ (toSynth a') (toSynth b') j
          - synthPipeExact n (toSynth a) (toSynth b) j) := by
      rw [smul_sub]
    rw [this, norm_smul, Complex.norm_natCast, Nat.cast_pow, Nat.cast_ofNat]
    gcongr
    exact hpipe j
  have hW : ‖ofSynth inner' k - ofSynth inner k‖
      ≤ (2 ^ n : ℝ) * ((4 * n + 2 * εa + 4) / 2 ^ p) := by
    rw [ofSynth_sub]
    exact (norm_ofSynth_apply_le _ k).trans (hinnerErr k.1)
  have hWexact : ‖ofSynth inner k‖ ≤ 1 := by
    have h := norm_dftNorm2_le hu k
    rw [hchain, norm_mul, Complex.norm_conj, norm_chirp2, one_mul] at h
    exact h
  -- step 4: post-multiplication with rounding
  have hx' : ‖(starRingEnd ℂ) (a' k)‖ ≤ 1 := by rw [Complex.norm_conj]; exact ha1 k
  have hxx : ‖(starRingEnd ℂ) (a' k) - (starRingEnd ℂ) (a k)‖ ≤ εa / 2 ^ p := by
    rw [← map_sub, Complex.norm_conj, le_div_iff₀ hp, mul_comm]; exact ha k
  have hfinal : ‖transform2Num n p e₁ e₂ e₃ a' u k - dftNorm2 (2 ^ n) r u k‖
      ≤ 2 / 2 ^ p + (2 ^ n : ℝ) * ((4 * n + 2 * εa + 4) / 2 ^ p) + εa / 2 ^ p := by
    rw [hchain]
    have e : rhoC p ((starRingEnd ℂ) (a' k) * ofSynth inner' k)
        - (starRingEnd ℂ) (a k) * ofSynth inner k
        = (rhoC p ((starRingEnd ℂ) (a' k) * ofSynth inner' k)
            - (starRingEnd ℂ) (a' k) * ofSynth inner' k)
          + (starRingEnd ℂ) (a' k) * (ofSynth inner' k - ofSynth inner k)
          + ((starRingEnd ℂ) (a' k) - (starRingEnd ℂ) (a k)) * ofSynth inner k := by
      ring
    show ‖rhoC p ((starRingEnd ℂ) (a' k) * ofSynth inner' k)
        - (starRingEnd ℂ) (a k) * ofSynth inner k‖ ≤ _
    rw [e]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_mul, norm_mul]
    have h1 := norm_rhoC_sub_le_two p ((starRingEnd ℂ) (a' k) * ofSynth inner' k)
    calc ‖rhoC p ((starRingEnd ℂ) (a' k) * ofSynth inner' k)
            - (starRingEnd ℂ) (a' k) * ofSynth inner' k‖
          + ‖(starRingEnd ℂ) (a' k)‖ * ‖ofSynth inner' k - ofSynth inner k‖
          + ‖(starRingEnd ℂ) (a' k) - (starRingEnd ℂ) (a k)‖ * ‖ofSynth inner k‖
        ≤ 2 / 2 ^ p + 1 * ((2 ^ n : ℝ) * ((4 * n + 2 * εa + 4) / 2 ^ p)) + εa / 2 ^ p * 1 := by
          gcongr
      _ = 2 / 2 ^ p + (2 ^ n : ℝ) * ((4 * n + 2 * εa + 4) / 2 ^ p) + εa / 2 ^ p := by ring
  calc 2 ^ p * ‖transform2Num n p e₁ e₂ e₃ a' u k - dftNorm2 (2 ^ n) r u k‖
      ≤ 2 ^ p * (2 / 2 ^ p + (2 ^ n : ℝ) * ((4 * n + 2 * εa + 4) / 2 ^ p) + εa / 2 ^ p) := by
        gcongr
    _ = (2 ^ n : ℝ) * (4 * n + 2 * εa + 4) + εa + 2 := by
        field_simp; ring

/-- With chirp error `εa ≤ 2`: scaled error at most `4 t n + 8 t + 4`. -/
theorem transform2_err_simple {n p : ℕ} {εa : ℝ} (ht2 : 2 ∣ 2 ^ n) (hr2 : 2 ∣ r)
    (htr : 2 ^ n ∣ 2 * r) (hn : (n : ℝ) ≤ 2 ^ p)
    {e₁ e₂ e₃ : (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)}
    (he₁ : ∀ m k, ‖e₁ m k‖ ≤ 1 / 2 ^ p) (he₂ : ∀ m k, ‖e₂ m k‖ ≤ 1 / 2 ^ p)
    (he₃ : ∀ m k, ‖e₃ m k‖ ≤ 1 / 2 ^ p)
    {a' u : Fin (2 ^ n) × Fin r → ℂ}
    (ha : ∀ j, 2 ^ p * ‖a' j - chirp2 (2 ^ n) r j‖ ≤ εa) (hεa : εa ≤ 2)
    (ha1 : ∀ j, ‖a' j‖ ≤ 1) (hu : ∀ j, ‖u j‖ ≤ 1) (k : Fin (2 ^ n) × Fin r) :
    2 ^ p * ‖transform2Num n p e₁ e₂ e₃ a' u k - dftNorm2 (2 ^ n) r u k‖
      ≤ 4 * (2 ^ n : ℝ) * n + 8 * 2 ^ n + 4 := by
  have h := transform2_err ht2 hr2 htr hn he₁ he₂ he₃ ha ha1 hu k
  have hpos : (0 : ℝ) ≤ 2 ^ n := by positivity
  calc 2 ^ p * ‖transform2Num n p e₁ e₂ e₃ a' u k - dftNorm2 (2 ^ n) r u k‖
      ≤ (2 ^ n : ℝ) * (4 * n + 2 * εa + 4) + εa + 2 := h
    _ ≤ (2 ^ n : ℝ) * (4 * n + 2 * 2 + 4) + 2 + 2 := by gcongr
    _ = 4 * (2 ^ n : ℝ) * n + 8 * 2 ^ n + 4 := by ring

end Numeric

end IntegerMultBounds.NLogN
