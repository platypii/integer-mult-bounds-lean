import IntegerMultBounds.NLogN.Bluestein
import IntegerMultBounds.NLogN.Approx

/-! Error bookkeeping for Bluestein's method, the proof of Theorem 3.1 of
Harvey and van der Hoeven. With the normalized transform `(1/t) F` and the
normalized convolution `(1/t) a ∗ b`, an approximate chirp with scaled error
`εa`, an approximate normalized convolution with scaled error `εM` that keeps
the unit ball, and rounded pointwise products, the pipeline
`round(ā · M̃(ã, round(ā · u)))` approximates the normalized transform with
scaled error at most `εM + 3 εa + 4`, in one and `d` dimensions. The
construction of the approximate chirp and convolution, and any cost, are not
part of this file. -/

namespace IntegerMultBounds.NLogN

open Complex Real

variable {t : ℕ} [NeZero t]

/-- The paper's normalized transform `(F_t u)_k = t⁻¹ ∑_j e^{-2πi jk/t} u_j`. -/
noncomputable def dftNorm (t : ℕ) [NeZero t] (u : ZMod t → ℂ) : ZMod t → ℂ :=
  fun k => (1 / t : ℂ) * dft (Complex.exp (-2 * π * I / t)) u k

/-- The paper's normalized convolution `M(a, b) = (1/t) a ∗ b`. -/
noncomputable def convNorm (t : ℕ) [NeZero t] (a b : ZMod t → ℂ) : ZMod t → ℂ :=
  fun k => (1 / t : ℂ) * cconv a b k

omit [NeZero t] in
theorem norm_chirp (j : ZMod t) : ‖chirp t j‖ = 1 := by
  unfold chirp
  have : π * I * ((j.val ^ 2 : ℕ) : ℂ) / t = ((π * (j.val ^ 2 : ℕ) / t : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- Bluestein with the normalization: `(1/t) F u = ā · ((1/t) a ∗ (ā · u))`. -/
theorem bluestein_norm (ht : 2 ∣ t) (u : ZMod t → ℂ) :
    dftNorm t u = fun k => (starRingEnd ℂ) (chirp t k) *
      convNorm t (chirp t) (fun j => (starRingEnd ℂ) (chirp t j) * u j) k := by
  funext k
  have h := congrFun (bluestein ht u) k
  simp only [dftNorm, convNorm]
  rw [h]
  ring

theorem norm_one_div_nat (n : ℕ) : ‖(1 / n : ℂ)‖ = 1 / n := by
  rw [norm_div, norm_one, Complex.norm_natCast]

/-- The normalized convolution is bounded by the product of sup bounds. -/
theorem norm_convNorm_le' {x y : ZMod t → ℂ} {X Y : ℝ} (hx : ∀ j, ‖x j‖ ≤ X)
    (hy : ∀ j, ‖y j‖ ≤ Y) (hX : 0 ≤ X) (_hY : 0 ≤ Y) (k : ZMod t) :
    ‖convNorm t x y k‖ ≤ X * Y := by
  have ht : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  simp only [convNorm, cconv]
  rw [norm_mul, norm_one_div_nat]
  calc 1 / (t : ℝ) * ‖∑ i, x i * y (k - i)‖ ≤ 1 / (t : ℝ) * ∑ i : ZMod t, X * Y := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul]
        exact mul_le_mul (hx i) (hy _) (norm_nonneg _) hX
    _ = X * Y := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        field_simp

theorem norm_convNorm_le {a b : ZMod t → ℂ} (ha : ∀ j, ‖a j‖ ≤ 1) (hb : ∀ j, ‖b j‖ ≤ 1)
    (k : ZMod t) : ‖convNorm t a b k‖ ≤ 1 := by
  simpa using norm_convNorm_le' ha hb zero_le_one zero_le_one k

theorem convNorm_sub_left (x x' y : ZMod t → ℂ) (k : ZMod t) :
    convNorm t (fun i => x i - x' i) y k = convNorm t x y k - convNorm t x' y k := by
  simp only [convNorm, cconv, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem convNorm_sub_right (x y y' : ZMod t → ℂ) (k : ZMod t) :
    convNorm t x (fun i => y i - y' i) k = convNorm t x y k - convNorm t x y' k := by
  simp only [convNorm, cconv, mul_sub, Finset.sum_sub_distrib]

/-- The approximate Bluestein pipeline: an approximate chirp `a'`, an approximate
normalized convolution `M'`, and rounded pointwise products. -/
noncomputable def bluesteinApprox (p : ℕ) (a' : ZMod t → ℂ)
    (M' : (ZMod t → ℂ) → (ZMod t → ℂ) → (ZMod t → ℂ)) (u : ZMod t → ℂ) : ZMod t → ℂ :=
  fun k => rhoC p ((starRingEnd ℂ) (a' k) *
    M' a' (fun j => rhoC p ((starRingEnd ℂ) (a' j) * u j)) k)

omit [NeZero t] in
theorem norm_conj_sub (x y : ℂ) : ‖(starRingEnd ℂ) x - (starRingEnd ℂ) y‖ = ‖x - y‖ := by
  rw [← map_sub, Complex.norm_conj]

/-- Scaled error of the Bluestein pipeline: `εM + 3 εa + 4`. -/
theorem bluesteinApprox_err {p : ℕ} {εa εM : ℝ} (ht : 2 ∣ t) {a' : ZMod t → ℂ}
    {M' : (ZMod t → ℂ) → (ZMod t → ℂ) → (ZMod t → ℂ)} {u : ZMod t → ℂ}
    (ha : ∀ j, 2 ^ p * ‖a' j - chirp t j‖ ≤ εa) (ha1 : ∀ j, ‖a' j‖ ≤ 1)
    (hM : ∀ x y, (∀ j, ‖x j‖ ≤ 1) → (∀ j, ‖y j‖ ≤ 1) →
      ∀ k, 2 ^ p * ‖M' x y k - convNorm t x y k‖ ≤ εM)
    (hM1 : ∀ x y, (∀ j, ‖x j‖ ≤ 1) → (∀ j, ‖y j‖ ≤ 1) → ∀ k, ‖M' x y k‖ ≤ 1)
    (hu : ∀ j, ‖u j‖ ≤ 1) (k : ZMod t) :
    2 ^ p * ‖bluesteinApprox p a' M' u k - dftNorm t u k‖ ≤ εM + 3 * εa + 4 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hεa : 0 ≤ εa := le_trans (by positivity) (ha k)
  set b : ZMod t → ℂ := fun j => (starRingEnd ℂ) (chirp t j) * u j with hb
  set b' : ZMod t → ℂ := fun j => rhoC p ((starRingEnd ℂ) (a' j) * u j) with hb'
  have hb'1 : ∀ j, ‖b' j‖ ≤ 1 := fun j => by
    refine (norm_rhoC_le _ _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul (ha1 j) (hu j) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hb1 : ∀ j, ‖b j‖ ≤ 1 := fun j => by
    simp only [hb, norm_mul, Complex.norm_conj, norm_chirp, one_mul]
    exact hu j
  have hbb : ∀ j, 2 ^ p * ‖b' j - b j‖ ≤ 2 + εa + 0 := fun j =>
    approx_mul_round (by rw [Complex.norm_conj]; exact ha1 j) (hu j)
      (by rw [Complex.norm_conj, norm_chirp]) (by rw [norm_conj_sub]; exact ha j)
      (by simp)
  set c := convNorm t (chirp t) b with hc
  set c' := M' a' b' with hc'
  have hc'1 : ∀ j, ‖c' j‖ ≤ 1 := hM1 a' b' ha1 hb'1
  have hc1 : ∀ j, ‖c j‖ ≤ 1 := fun j =>
    norm_convNorm_le (fun i => (norm_chirp i).le) hb1 j
  have hcc : ∀ j, 2 ^ p * ‖c' j - c j‖ ≤ εM + (εa + (2 + εa)) := by
    intro j
    have h1 := hM a' b' ha1 hb'1 j
    have h2 : 2 ^ p * ‖convNorm t a' b' j - convNorm t (chirp t) b j‖ ≤ εa + (2 + εa) := by
      have e : convNorm t a' b' j - convNorm t (chirp t) b j =
          convNorm t (fun i => a' i - chirp t i) b' j +
            convNorm t (chirp t) (fun i => b' i - b i) j := by
        rw [convNorm_sub_left, convNorm_sub_right]
        ring
      have hA : ∀ i, ‖a' i - chirp t i‖ ≤ εa / 2 ^ p := fun i => by
        rw [le_div_iff₀ hp, mul_comm]
        exact ha i
      have hB : ∀ i, ‖b' i - b i‖ ≤ (2 + εa + 0) / 2 ^ p := fun i => by
        rw [le_div_iff₀ hp, mul_comm]
        exact hbb i
      have hX : 0 ≤ εa / 2 ^ p := by positivity
      have hY : 0 ≤ (2 + εa + 0) / 2 ^ p := by positivity
      rw [e]
      calc 2 ^ p * ‖convNorm t (fun i => a' i - chirp t i) b' j +
              convNorm t (chirp t) (fun i => b' i - b i) j‖
          ≤ 2 ^ p * (‖convNorm t (fun i => a' i - chirp t i) b' j‖ +
              ‖convNorm t (chirp t) (fun i => b' i - b i) j‖) := by
            gcongr
            exact norm_add_le _ _
        _ ≤ 2 ^ p * (εa / 2 ^ p * 1 + 1 * ((2 + εa + 0) / 2 ^ p)) := by
            gcongr
            · exact norm_convNorm_le' hA hb'1 hX zero_le_one j
            · exact norm_convNorm_le' (fun i => (norm_chirp i).le) hB zero_le_one hY j
        _ = εa + (2 + εa) := by
            field_simp
            ring
    calc 2 ^ p * ‖c' j - c j‖
        = 2 ^ p * ‖(M' a' b' j - convNorm t a' b' j) +
            (convNorm t a' b' j - convNorm t (chirp t) b j)‖ := by
          simp only [hc', hc]
          ring_nf
      _ ≤ 2 ^ p * ‖M' a' b' j - convNorm t a' b' j‖ +
            2 ^ p * ‖convNorm t a' b' j - convNorm t (chirp t) b j‖ := by
          rw [← mul_add]
          gcongr
          exact norm_add_le _ _
      _ ≤ εM + (εa + (2 + εa)) := add_le_add h1 h2
  have hfinal := approx_mul_round (p := p) (η₁ := εa) (η₂ := εM + (εa + (2 + εa)))
    (u' := (starRingEnd ℂ) (a' k)) (v' := c' k) (u := (starRingEnd ℂ) (chirp t k)) (v := c k)
    (by rw [Complex.norm_conj]; exact ha1 k) (hc'1 k)
    (by rw [Complex.norm_conj, norm_chirp]) (by rw [norm_conj_sub]; exact ha k) (hcc k)
  have hgoal : bluesteinApprox p a' M' u k - dftNorm t u k =
      rhoC p ((starRingEnd ℂ) (a' k) * c' k) - (starRingEnd ℂ) (chirp t k) * c k := by
    rw [bluestein_norm ht]
    rfl
  rw [hgoal]
  linarith

section MultiDim

variable {d : ℕ} {N : Fin d → ℕ} [∀ i, NeZero (N i)]

/-- The normalized `d`-dimensional transform `(1/T) F`, `T = ∏ N i`. -/
noncomputable def dftNormD (N : Fin d → ℕ) [∀ i, NeZero (N i)]
    (u : ((i : Fin d) → ZMod (N i)) → ℂ) : ((i : Fin d) → ZMod (N i)) → ℂ :=
  fun k => (1 / (∏ i, N i : ℕ) : ℂ) * dftD (fun i => Complex.exp (-2 * π * I / (N i))) u k

/-- The normalized `d`-dimensional convolution `(1/T) a ∗ b`. -/
noncomputable def convNormD (N : Fin d → ℕ) [∀ i, NeZero (N i)]
    (a b : ((i : Fin d) → ZMod (N i)) → ℂ) : ((i : Fin d) → ZMod (N i)) → ℂ :=
  fun k => (1 / (∏ i, N i : ℕ) : ℂ) * convG a b k

omit [∀ i, NeZero (N i)] in
theorem norm_chirpD (j : (i : Fin d) → ZMod (N i)) : ‖chirpD N j‖ = 1 := by
  simp only [chirpD, norm_prod, norm_chirp, Finset.prod_const_one]

theorem bluesteinD_norm (hN : ∀ i, 2 ∣ N i) (u : ((i : Fin d) → ZMod (N i)) → ℂ) :
    dftNormD N u = fun k => (starRingEnd ℂ) (chirpD N k) *
      convNormD N (chirpD N) (fun j => (starRingEnd ℂ) (chirpD N j) * u j) k := by
  funext k
  have h := congrFun (bluesteinD hN u) k
  simp only [dftNormD, convNormD]
  rw [h]
  ring

theorem card_pi_zmod : Fintype.card ((i : Fin d) → ZMod (N i)) = ∏ i, N i := by
  rw [Fintype.card_pi]
  simp only [ZMod.card]

theorem norm_convNormD_le' {x y : ((i : Fin d) → ZMod (N i)) → ℂ} {X Y : ℝ}
    (hx : ∀ j, ‖x j‖ ≤ X) (hy : ∀ j, ‖y j‖ ≤ Y) (hX : 0 ≤ X) (_hY : 0 ≤ Y)
    (k : (i : Fin d) → ZMod (N i)) : ‖convNormD N x y k‖ ≤ X * Y := by
  have hT : ((∏ i, N i : ℕ) : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (N i)
  simp only [convNormD, convG]
  rw [norm_mul, norm_one_div_nat]
  calc 1 / ((∏ i, N i : ℕ) : ℝ) * ‖∑ i, x i * y (k - i)‖
      ≤ 1 / ((∏ i, N i : ℕ) : ℝ) * ∑ _i : (i : Fin d) → ZMod (N i), X * Y := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul]
        exact mul_le_mul (hx i) (hy _) (norm_nonneg _) hX
    _ = X * Y := by
        rw [Finset.sum_const, Finset.card_univ, card_pi_zmod, nsmul_eq_mul]
        field_simp

theorem norm_convNormD_le {a b : ((i : Fin d) → ZMod (N i)) → ℂ} (ha : ∀ j, ‖a j‖ ≤ 1)
    (hb : ∀ j, ‖b j‖ ≤ 1) (k : (i : Fin d) → ZMod (N i)) : ‖convNormD N a b k‖ ≤ 1 := by
  simpa using norm_convNormD_le' ha hb zero_le_one zero_le_one k

theorem convNormD_sub_left (x x' y : ((i : Fin d) → ZMod (N i)) → ℂ)
    (k : (i : Fin d) → ZMod (N i)) :
    convNormD N (fun i => x i - x' i) y k = convNormD N x y k - convNormD N x' y k := by
  simp only [convNormD, convG, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem convNormD_sub_right (x y y' : ((i : Fin d) → ZMod (N i)) → ℂ)
    (k : (i : Fin d) → ZMod (N i)) :
    convNormD N x (fun i => y i - y' i) k = convNormD N x y k - convNormD N x y' k := by
  simp only [convNormD, convG, mul_sub, Finset.sum_sub_distrib]

/-- The approximate `d`-dimensional Bluestein pipeline. -/
noncomputable def bluesteinApproxD (p : ℕ) (a' : ((i : Fin d) → ZMod (N i)) → ℂ)
    (M' : (((i : Fin d) → ZMod (N i)) → ℂ) → (((i : Fin d) → ZMod (N i)) → ℂ) →
      (((i : Fin d) → ZMod (N i)) → ℂ))
    (u : ((i : Fin d) → ZMod (N i)) → ℂ) : ((i : Fin d) → ZMod (N i)) → ℂ :=
  fun k => rhoC p ((starRingEnd ℂ) (a' k) *
    M' a' (fun j => rhoC p ((starRingEnd ℂ) (a' j) * u j)) k)

/-- Scaled error of the `d`-dimensional Bluestein pipeline: `εM + 3 εa + 4`. -/
theorem bluesteinApproxD_err {p : ℕ} {εa εM : ℝ} (hN : ∀ i, 2 ∣ N i)
    {a' : ((i : Fin d) → ZMod (N i)) → ℂ}
    {M' : (((i : Fin d) → ZMod (N i)) → ℂ) → (((i : Fin d) → ZMod (N i)) → ℂ) →
      (((i : Fin d) → ZMod (N i)) → ℂ)}
    {u : ((i : Fin d) → ZMod (N i)) → ℂ}
    (ha : ∀ j, 2 ^ p * ‖a' j - chirpD N j‖ ≤ εa) (ha1 : ∀ j, ‖a' j‖ ≤ 1)
    (hM : ∀ x y, (∀ j, ‖x j‖ ≤ 1) → (∀ j, ‖y j‖ ≤ 1) →
      ∀ k, 2 ^ p * ‖M' x y k - convNormD N x y k‖ ≤ εM)
    (hM1 : ∀ x y, (∀ j, ‖x j‖ ≤ 1) → (∀ j, ‖y j‖ ≤ 1) → ∀ k, ‖M' x y k‖ ≤ 1)
    (hu : ∀ j, ‖u j‖ ≤ 1) (k : (i : Fin d) → ZMod (N i)) :
    2 ^ p * ‖bluesteinApproxD p a' M' u k - dftNormD N u k‖ ≤ εM + 3 * εa + 4 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hεa : 0 ≤ εa := le_trans (by positivity) (ha k)
  set b : ((i : Fin d) → ZMod (N i)) → ℂ := fun j => (starRingEnd ℂ) (chirpD N j) * u j with hb
  set b' : ((i : Fin d) → ZMod (N i)) → ℂ :=
    fun j => rhoC p ((starRingEnd ℂ) (a' j) * u j) with hb'
  have hb'1 : ∀ j, ‖b' j‖ ≤ 1 := fun j => by
    refine (norm_rhoC_le _ _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul (ha1 j) (hu j) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hb1 : ∀ j, ‖b j‖ ≤ 1 := fun j => by
    simp only [hb, norm_mul, Complex.norm_conj, norm_chirpD, one_mul]
    exact hu j
  have hbb : ∀ j, 2 ^ p * ‖b' j - b j‖ ≤ 2 + εa + 0 := fun j =>
    approx_mul_round (by rw [Complex.norm_conj]; exact ha1 j) (hu j)
      (by rw [Complex.norm_conj, norm_chirpD]) (by rw [norm_conj_sub]; exact ha j)
      (by simp)
  set c := convNormD N (chirpD N) b with hc
  set c' := M' a' b' with hc'
  have hc'1 : ∀ j, ‖c' j‖ ≤ 1 := hM1 a' b' ha1 hb'1
  have hcc : ∀ j, 2 ^ p * ‖c' j - c j‖ ≤ εM + (εa + (2 + εa)) := by
    intro j
    have h1 := hM a' b' ha1 hb'1 j
    have h2 : 2 ^ p * ‖convNormD N a' b' j - convNormD N (chirpD N) b j‖ ≤
        εa + (2 + εa) := by
      have e : convNormD N a' b' j - convNormD N (chirpD N) b j =
          convNormD N (fun i => a' i - chirpD N i) b' j +
            convNormD N (chirpD N) (fun i => b' i - b i) j := by
        rw [convNormD_sub_left, convNormD_sub_right]
        ring
      have hA : ∀ i, ‖a' i - chirpD N i‖ ≤ εa / 2 ^ p := fun i => by
        rw [le_div_iff₀ hp, mul_comm]
        exact ha i
      have hB : ∀ i, ‖b' i - b i‖ ≤ (2 + εa + 0) / 2 ^ p := fun i => by
        rw [le_div_iff₀ hp, mul_comm]
        exact hbb i
      have hX : 0 ≤ εa / 2 ^ p := by positivity
      have hY : 0 ≤ (2 + εa + 0) / 2 ^ p := by positivity
      rw [e]
      calc 2 ^ p * ‖convNormD N (fun i => a' i - chirpD N i) b' j +
              convNormD N (chirpD N) (fun i => b' i - b i) j‖
          ≤ 2 ^ p * (‖convNormD N (fun i => a' i - chirpD N i) b' j‖ +
              ‖convNormD N (chirpD N) (fun i => b' i - b i) j‖) := by
            gcongr
            exact norm_add_le _ _
        _ ≤ 2 ^ p * (εa / 2 ^ p * 1 + 1 * ((2 + εa + 0) / 2 ^ p)) := by
            gcongr
            · exact norm_convNormD_le' hA hb'1 hX zero_le_one j
            · exact norm_convNormD_le' (fun i => (norm_chirpD i).le) hB zero_le_one hY j
        _ = εa + (2 + εa) := by
            field_simp
            ring
    calc 2 ^ p * ‖c' j - c j‖
        = 2 ^ p * ‖(M' a' b' j - convNormD N a' b' j) +
            (convNormD N a' b' j - convNormD N (chirpD N) b j)‖ := by
          simp only [hc', hc]
          ring_nf
      _ ≤ 2 ^ p * ‖M' a' b' j - convNormD N a' b' j‖ +
            2 ^ p * ‖convNormD N a' b' j - convNormD N (chirpD N) b j‖ := by
          rw [← mul_add]
          gcongr
          exact norm_add_le _ _
      _ ≤ εM + (εa + (2 + εa)) := add_le_add h1 h2
  have hfinal := approx_mul_round (p := p) (η₁ := εa) (η₂ := εM + (εa + (2 + εa)))
    (u' := (starRingEnd ℂ) (a' k)) (v' := c' k) (u := (starRingEnd ℂ) (chirpD N k)) (v := c k)
    (by rw [Complex.norm_conj]; exact ha1 k) (hc'1 k)
    (by rw [Complex.norm_conj, norm_chirpD]) (by rw [norm_conj_sub]; exact ha k) (hcc k)
  have hgoal : bluesteinApproxD p a' M' u k - dftNormD N u k =
      rhoC p ((starRingEnd ℂ) (a' k) * c' k) - (starRingEnd ℂ) (chirpD N k) * c k := by
    rw [bluesteinD_norm hN]
    rfl
  rw [hgoal]
  linarith

end MultiDim

end IntegerMultBounds.NLogN
