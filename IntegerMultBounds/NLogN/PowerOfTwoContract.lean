import IntegerMultBounds.NLogN.PowerOfTwoNumericD
import IntegerMultBounds.NLogN.ExplicitNumeric
import IntegerMultBounds.NLogN.MainTransform

/-! The explicit numerical power-of-two transform packaged as the `Ft'` the
recursive step needs. Lengths are `2^(Fin.snoc e g i)`: exponents `e` for the
first `d` coordinates and `g` for the last, the synthetic ring dimension.
Proved: the normalized transform operator `dftDCLM` is `dftNormD`; the rounded
chirp is within two scaled units of the chirp and in the unit ball;
transporting a numerical one-dimensional synthetic transform along an equality
of lengths preserves its approximation error and unit-ball property, so the
clamped synthetic FFTs give numerical `d`-dimensional transforms on the chain's
own index type with scaled error `∑ e_i`; hence the clamped Bluestein transform
approximates `dftDCLM` with scaled error `2^(∑ e)(3 ∑ e + 8) + 4`, maps the unit
ball to itself, and this error is at most `8 T log₂ T` with `T = ∏ t_i`. Bit
costs are not modelled. -/

namespace IntegerMultBounds.NLogN

open Complex Real

section Identification

variable {d : ℕ}

/-- The normalized transform operator is the normalized transform of the Bluestein
file: the inverse of `e^{2πi/N}` is `e^{-2πi/N}`. -/
theorem dftDCLM_eq_dftNormD (N : Fin d → ℕ) [∀ i, NeZero (N i)]
    (u : ((i : Fin d) → ZMod (N i)) → ℂ) : dftDCLM N u = dftNormD N u := by
  rw [dftDCLM_apply]
  funext k
  simp only [dftNormD]
  congr 2
  funext i
  rw [← Complex.exp_neg]
  congr 1
  ring

end Identification

section Chirp

variable {d : ℕ} {N : Fin d → ℕ} [∀ i, NeZero (N i)]

/-- The rounded chirp. -/
noncomputable def chirpNum (p : ℕ) (N : Fin d → ℕ) [∀ i, NeZero (N i)]
    (j : (i : Fin d) → ZMod (N i)) : ℂ :=
  rhoC p (chirpD N j)

theorem chirpNum_err (p : ℕ) (j : (i : Fin d) → ZMod (N i)) :
    2 ^ p * ‖chirpNum p N j - chirpD N j‖ ≤ 2 := by
  have h := norm_rhoC_sub_le_two p (chirpD N j)
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  rw [le_div_iff₀ hp] at h
  simpa [chirpNum, mul_comm] using h

theorem norm_chirpNum_le (p : ℕ) (j : (i : Fin d) → ZMod (N i)) : ‖chirpNum p N j‖ ≤ 1 :=
  (norm_rhoC_le p _).trans (norm_chirpD j).le

end Chirp

section Reindex

variable {r : ℕ} [NeZero r]

omit [NeZero r] in
/-- Precomposition is contractive in the sup norm, vector-valued version. -/
theorem norm_comp_le_vec {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ)
    (x : κ → (Fin r → ℂ)) : ‖x ∘ f‖ ≤ ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  exact norm_le_pi_norm x (f i)

/-- Transport a map on `Fin t'`-indexed arrays to `Fin t`-indexed ones along `t = t'`. -/
noncomputable def reindex1 {t t' : ℕ} (h : t = t')
    (F : (Fin t' → (Fin r → ℂ)) → (Fin t' → (Fin r → ℂ))) :
    (Fin t → (Fin r → ℂ)) → (Fin t → (Fin r → ℂ)) :=
  fun w => F (w ∘ (finCongr h).symm) ∘ finCongr h

theorem finCongr_rfl_apply {t : ℕ} (k : Fin t) : finCongr (rfl : t = t) k = k :=
  Fin.ext (finCongr_apply_coe rfl k)

theorem finCongr_rfl_symm_apply {t : ℕ} (k : Fin t) : (finCongr (rfl : t = t)).symm k = k := by
  apply (finCongr (rfl : t = t)).injective
  rw [Equiv.apply_symm_apply, finCongr_rfl_apply]

omit [NeZero r] in
/-- The synthetic transform commutes with relabelling along an equality of lengths. -/
theorem synthDFT_reindex {t t' : ℕ} (h : t = t') (w : Fin t → (Fin r → ℂ)) :
    synthDFT r t w = synthDFT r t' (w ∘ (finCongr h).symm) ∘ finCongr h := by
  subst h
  funext j
  show synthDFT r t w j = synthDFT r t (fun k => w ((finCongr (rfl : t = t)).symm k))
    (finCongr (rfl : t = t) j)
  simp only [finCongr_rfl_symm_apply, finCongr_rfl_apply]

/-- Transporting an approximation of the synthetic transform keeps its error. -/
theorem approxMap_reindex1 {p : ℕ} {ε : ℝ} {t t' : ℕ} (h : t = t')
    {F : (Fin t' → (Fin r → ℂ)) → (Fin t' → (Fin r → ℂ))}
    (hF : ApproxMap p F (synthDFTCLM r t') ε) :
    ApproxMap p (reindex1 h F) (synthDFTCLM r t) ε := by
  intro w hw
  have hw' : ‖w ∘ (finCongr h).symm‖ ≤ 1 := (norm_comp_le_vec (⇑(finCongr h).symm) w).trans hw
  have h1 := hF (w ∘ (finCongr h).symm) hw'
  rw [synthDFTCLM_apply] at h1 ⊢
  rw [synthDFT_reindex h w]
  calc (2 : ℝ) ^ p * ‖reindex1 h F w - synthDFT r t' (w ∘ (finCongr h).symm) ∘ finCongr h‖
      = 2 ^ p * ‖(F (w ∘ (finCongr h).symm) - synthDFT r t' (w ∘ (finCongr h).symm)) ∘ finCongr h‖ :=
        rfl
    _ ≤ 2 ^ p * ‖F (w ∘ (finCongr h).symm) - synthDFT r t' (w ∘ (finCongr h).symm)‖ := by
        gcongr
        exact norm_comp_le_vec (⇑(finCongr h)) _
    _ ≤ ε := h1

omit [NeZero r] in
theorem reindex1_ball {t t' : ℕ} (h : t = t')
    {F : (Fin t' → (Fin r → ℂ)) → (Fin t' → (Fin r → ℂ))}
    (hF : ∀ w, ‖w‖ ≤ 1 → ‖F w‖ ≤ 1) (w : Fin t → (Fin r → ℂ)) (hw : ‖w‖ ≤ 1) :
    ‖reindex1 h F w‖ ≤ 1 :=
  (norm_comp_le_vec (⇑(finCongr h)) (F (w ∘ (finCongr h).symm))).trans
    (hF _ ((norm_comp_le_vec (⇑(finCongr h).symm) w).trans hw))

end Reindex

section Lengths

variable {d : ℕ}

/-- The lengths `2^e_i` of the first `d` coordinates and `2^g` of the last. -/
def lenOf (e : Fin d → ℕ) (g : ℕ) : Fin (d + 1) → ℕ :=
  fun i => 2 ^ (Fin.snoc (α := fun _ => ℕ) e g i)

/-- The predecessor family, so that `lenAll (Mof e g) = lenOf e g`. -/
def Mof (e : Fin d → ℕ) (g : ℕ) : Fin (d + 1) → ℕ :=
  fun i => lenOf e g i - 1

theorem lenAll_Mof (e : Fin d → ℕ) (g : ℕ) : lenAll (Mof e g) = lenOf e g := by
  funext i
  simp only [lenAll, Mof]
  exact Nat.sub_add_cancel Nat.one_le_two_pow

theorem lenInit_Mof (e : Fin d → ℕ) (g : ℕ) (i : Fin d) : lenInit (Mof e g) i = 2 ^ e i := by
  simp only [lenInit, Mof, lenOf, Fin.snoc_castSucc]
  exact Nat.sub_add_cancel Nat.one_le_two_pow

theorem lenLast_Mof (e : Fin d → ℕ) (g : ℕ) : lenLast (Mof e g) = 2 ^ g := by
  simp only [lenLast, Mof, lenOf, Fin.snoc_last]
  exact Nat.sub_add_cancel Nat.one_le_two_pow

theorem Mof_add_one (e : Fin d → ℕ) (g : ℕ) (i : Fin (d + 1)) :
    Mof e g i + 1 = 2 ^ (Fin.snoc (α := fun _ => ℕ) e g i) := by
  simp only [Mof, lenOf]
  exact Nat.sub_add_cancel Nat.one_le_two_pow

theorem prod_lenInit_Mof (e : Fin d → ℕ) (g : ℕ) :
    ∏ i, lenInit (Mof e g) i = 2 ^ (∑ i, e i) := by
  simp only [lenInit_Mof]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem prod_lenOf (e : Fin d → ℕ) (g : ℕ) : ∏ i, lenOf e g i = 2 ^ (∑ i, e i + g) := by
  rw [← lenAll_Mof, prod_lenAll, prod_lenInit_Mof, lenLast_Mof, pow_add]

theorem log_prod_lenOf (e : Fin d → ℕ) (g : ℕ) :
    Nat.log 2 (∏ i, lenOf e g i) = ∑ i, e i + g := by
  rw [prod_lenOf, Nat.log_pow one_lt_two]

theorem hpow_Mof (e : Fin d → ℕ) (g : ℕ) : ∀ i, ∃ f, Mof e g i + 1 = 2 ^ f :=
  fun i => ⟨_, Mof_add_one e g i⟩

theorem heven_Mof (e : Fin d → ℕ) (g : ℕ) (he : ∀ i, 1 ≤ e i) (hg : 1 ≤ g) :
    ∀ i, 2 ∣ Mof e g i + 1 := by
  intro i
  rw [Mof_add_one]
  refine dvd_pow_self 2 ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]; omega
  · rw [Fin.snoc_castSucc]; have := he j; omega

theorem hdiv_Mof (e : Fin d → ℕ) (g : ℕ) (hdiv : ∀ i, 2 ^ e i ∣ 2 * 2 ^ g) :
    ∀ i : Fin d, Mof e g (Fin.castSucc i) + 1 ∣ 2 * (Mof e g (Fin.last d) + 1) := by
  intro i
  rw [Mof_add_one, Mof_add_one, Fin.snoc_castSucc, Fin.snoc_last]
  exact hdiv i

end Lengths

section Contract

variable {d : ℕ}

/-- The numerical `d`-dimensional synthetic transform on the chain's own index type:
the clamped synthetic FFTs relabelled along `lenInit (Mof e g) i = 2^(e i)`. -/
noncomputable def synthNumChain (e : Fin d → ℕ) (g : ℕ)
    (E : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin (lenLast (Mof e g)) → ℂ)) :
    (((i : Fin d) → Fin (lenInit (Mof e g) i)) → (Fin (lenLast (Mof e g)) → ℂ)) →
      (((i : Fin d) → Fin (lenInit (Mof e g) i)) → (Fin (lenLast (Mof e g)) → ℂ)) :=
  tensorV d (lenInit (Mof e g)) fun i =>
    reindex1 (lenInit_Mof e g i) (synthFFTNumC (lenLast (Mof e g)) (e i) (E i))

theorem synthNumChain_ball (e : Fin d → ℕ) (g : ℕ)
    (E : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin (lenLast (Mof e g)) → ℂ))
    (w : ((i : Fin d) → Fin (lenInit (Mof e g) i)) → (Fin (lenLast (Mof e g)) → ℂ))
    (hw : ‖w‖ ≤ 1) : ‖synthNumChain e g E w‖ ≤ 1 :=
  tensorV_ball (V := Fin (lenLast (Mof e g)) → ℂ) d (lenInit (Mof e g))
    (fun i => reindex1 (lenInit_Mof e g i) (synthFFTNumC (lenLast (Mof e g)) (e i) (E i)))
    (fun _ v hv => reindex1_ball _ (fun u _ => synthFFTNumC_ball _ _ u) v hv) w hw

/-- Proposition 3.3 on the chain's index type: scaled error `∑ e_i`. -/
theorem approxMap_synthNumChain {p : ℕ} (e : Fin d → ℕ) (g : ℕ)
    (hdiv : ∀ i, 2 ^ e i ∣ 2 * 2 ^ g)
    {E : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin (lenLast (Mof e g)) → ℂ)}
    (hE : ∀ i m k, ‖E i m k‖ ≤ 1 / 2 ^ p) :
    ApproxMap p (synthNumChain e g E) (synthDFTDCLM (lenLast (Mof e g)) (lenInit (Mof e g)))
      (∑ i, (e i : ℝ)) := by
  have hr : ∀ i, 2 ^ e i ∣ 2 * lenLast (Mof e g) := by
    intro i; rw [lenLast_Mof]; exact hdiv i
  exact approxMap_tensorV d _ _ _ _ (fun i => opNorm_synthDFTCLM_le _)
    (fun i => approxMap_reindex1 _ (approxMap_synthFFTNumC (hr i) (hE i)))
    (fun i v hv => reindex1_ball _ (fun u _ => synthFFTNumC_ball _ _ u) v hv)

theorem synthNumChain_err {p : ℕ} (e : Fin d → ℕ) (g : ℕ)
    (hdiv : ∀ i, 2 ^ e i ∣ 2 * 2 ^ g)
    {E : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin (lenLast (Mof e g)) → ℂ)}
    (hE : ∀ i m k, ‖E i m k‖ ≤ 1 / 2 ^ p)
    (w : ((i : Fin d) → Fin (lenInit (Mof e g) i)) → (Fin (lenLast (Mof e g)) → ℂ))
    (hw : ‖w‖ ≤ 1) (k : (i : Fin d) → Fin (lenInit (Mof e g) i)) :
    2 ^ p * ‖synthNumChain e g E w k - synthDFTD (lenLast (Mof e g)) (lenInit (Mof e g)) w k‖
      ≤ ∑ i, (e i : ℝ) := by
  have h := approxMap_synthNumChain e g hdiv hE w hw
  rw [synthDFTDCLM_apply] at h
  calc (2 : ℝ) ^ p * ‖synthNumChain e g E w k - synthDFTD (lenLast (Mof e g)) (lenInit (Mof e g)) w k‖
      ≤ 2 ^ p * ‖synthNumChain e g E w - synthDFTD (lenLast (Mof e g)) (lenInit (Mof e g)) w‖ := by
        gcongr
        exact norm_le_pi_norm (synthNumChain e g E w - synthDFTD (lenLast (Mof e g)) (lenInit (Mof e g)) w) k
    _ ≤ ∑ i, (e i : ℝ) := h

/-- The explicit, clamped numerical power-of-two transform. -/
noncomputable def powerOfTwoNum (e : Fin d → ℕ) (g : ℕ) (p : ℕ)
    (E₁ E₂ E₃ : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin (lenLast (Mof e g)) → ℂ)) :
    (((i : Fin (d + 1)) → ZMod (Mof e g i + 1)) → ℂ) →
      (((i : Fin (d + 1)) → ZMod (Mof e g i + 1)) → ℂ) :=
  fun u => clampV (transformDNum (Mof e g) p (synthNumChain e g E₁) (synthNumChain e g E₂)
    (synthNumChain e g E₃) (chirpNum p (lenAll (Mof e g))) u)

theorem powerOfTwoNum_ball (e : Fin d → ℕ) (g : ℕ) (p : ℕ)
    (E₁ E₂ E₃ : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin (lenLast (Mof e g)) → ℂ))
    (u : ((i : Fin (d + 1)) → ZMod (Mof e g i + 1)) → ℂ) : ‖powerOfTwoNum e g p E₁ E₂ E₃ u‖ ≤ 1 :=
  norm_clampV_le_one _

/-- Theorem 3.1 as an approximation of the transform operator: scaled error
`2^(∑ e) (3 ∑ e + 8) + 4`. -/
theorem approxMap_powerOfTwoNum {p : ℕ} (e : Fin d → ℕ) (g : ℕ) (he : ∀ i, 1 ≤ e i)
    (hg : 1 ≤ g) (hdiv : ∀ i, 2 ^ e i ∣ 2 * 2 ^ g)
    {E₁ E₂ E₃ : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin (lenLast (Mof e g)) → ℂ)}
    (hE₁ : ∀ i m k, ‖E₁ i m k‖ ≤ 1 / 2 ^ p) (hE₂ : ∀ i m k, ‖E₂ i m k‖ ≤ 1 / 2 ^ p)
    (hE₃ : ∀ i m k, ‖E₃ i m k‖ ≤ 1 / 2 ^ p) :
    ApproxMap p (powerOfTwoNum e g p E₁ E₂ E₃) (dftDCLM (lenAll (Mof e g)))
      ((2 : ℝ) ^ (∑ i, e i) * (3 * ∑ i, (e i : ℝ) + 8) + 4) := by
  have hnorm : ‖dftDCLM (lenAll (Mof e g))‖ ≤ 1 := opNorm_dftDCLM_le
  refine approxMap_clamp hnorm ?_
  intro u hu
  have hu' : ∀ j, ‖u j‖ ≤ 1 := fun j => (norm_le_pi_norm u j).trans hu
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hT' : ((∏ i, lenInit (Mof e g) i : ℕ) : ℝ) = (2 : ℝ) ^ (∑ i, e i) := by
    rw [prod_lenInit_Mof]; push_cast; rfl
  have herr := fun k => transformD_err_simple (Mof e g) (p := p) (S := ∑ i, (e i : ℝ)) (εa := 2)
    (hpow_Mof e g) (heven_Mof e g he hg) (hdiv_Mof e g hdiv)
    (synthNumChain_err e g hdiv hE₁) (synthNumChain_err e g hdiv hE₂)
    (synthNumChain_err e g hdiv hE₃)
    (synthNumChain_ball e g E₁) (synthNumChain_ball e g E₂)
    (chirpNum_err p) le_rfl (norm_chirpNum_le p) hu' k
  rw [dftDCLM_eq_dftNormD]
  rw [mul_comm, ← le_div_iff₀ hp, pi_norm_le_iff_of_nonneg (by positivity)]
  intro k
  rw [le_div_iff₀ hp, mul_comm]
  calc (2 : ℝ) ^ p * ‖(transformDNum (Mof e g) p (synthNumChain e g E₁) (synthNumChain e g E₂)
        (synthNumChain e g E₃) (chirpNum p (lenAll (Mof e g))) u - dftNormD (lenAll (Mof e g)) u) k‖
      = 2 ^ p * ‖transformDNum (Mof e g) p (synthNumChain e g E₁) (synthNumChain e g E₂)
        (synthNumChain e g E₃) (chirpNum p (lenAll (Mof e g))) u k - dftNormD (lenAll (Mof e g)) u k‖ :=
        rfl
    _ ≤ 3 * ((∏ i, lenInit (Mof e g) i : ℕ) : ℝ) * (∑ i, (e i : ℝ))
        + 8 * ((∏ i, lenInit (Mof e g) i : ℕ) : ℝ) + 4 := herr k
    _ = (2 : ℝ) ^ (∑ i, e i) * (3 * ∑ i, (e i : ℝ) + 8) + 4 := by rw [hT']; ring

/-- The contract: a numerical transform of the power-of-two grid with the stated
error, mapping the unit ball to itself. -/
theorem powerOfTwo_contract {p : ℕ} (e : Fin d → ℕ) (g : ℕ) (he : ∀ i, 1 ≤ e i)
    (hg : 1 ≤ g) (hdiv : ∀ i, 2 ^ e i ∣ 2 * 2 ^ g)
    {E₁ E₂ E₃ : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin (lenLast (Mof e g)) → ℂ)}
    (hE₁ : ∀ i m k, ‖E₁ i m k‖ ≤ 1 / 2 ^ p) (hE₂ : ∀ i m k, ‖E₂ i m k‖ ≤ 1 / 2 ^ p)
    (hE₃ : ∀ i m k, ‖E₃ i m k‖ ≤ 1 / 2 ^ p) :
    ∃ Ft' : (((i : Fin (d + 1)) → ZMod (Mof e g i + 1)) → ℂ) →
        (((i : Fin (d + 1)) → ZMod (Mof e g i + 1)) → ℂ),
      ApproxMap p Ft' (dftDCLM (lenAll (Mof e g)))
        ((2 : ℝ) ^ (∑ i, e i) * (3 * ∑ i, (e i : ℝ) + 8) + 4) ∧
      ∀ u, ‖u‖ ≤ 1 → ‖Ft' u‖ ≤ 1 :=
  ⟨powerOfTwoNum e g p E₁ E₂ E₃, approxMap_powerOfTwoNum e g he hg hdiv hE₁ hE₂ hE₃,
    fun u _ => powerOfTwoNum_ball e g p E₁ E₂ E₃ u⟩

/-- The paper's bound: the error is at most `8 T log₂ T` with `T = ∏ t_i`. -/
theorem powerOfTwo_contract_bound_nat (e : Fin d → ℕ) (g : ℕ) (hg : 1 ≤ g)
    (hsum : 1 ≤ ∑ i, e i) :
    2 ^ (∑ i, e i) * (3 * ∑ i, e i + 8) + 4
      ≤ 8 * (∏ i, lenOf e g i) * Nat.log 2 (∏ i, lenOf e g i) := by
  rw [log_prod_lenOf, prod_lenOf, pow_add]
  set S := ∑ i, e i
  have hX : 2 ≤ 2 ^ S := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) hsum
  have hY : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  set X := 2 ^ S
  set Y := 2 ^ g
  have h1 : X * (3 * S + 8) + 4 ≤ 16 * X * S := by nlinarith
  have h2 : 16 * X * S ≤ 8 * (X * Y) * (S + g) := by
    have hXS : 0 ≤ X * S := Nat.zero_le _
    calc 16 * X * S = 8 * (X * 2) * S := by ring
      _ ≤ 8 * (X * Y) * S := by gcongr
      _ ≤ 8 * (X * Y) * (S + g) := by gcongr; omega
  exact h1.trans h2

theorem powerOfTwo_contract_bound (e : Fin d → ℕ) (g : ℕ) (hg : 1 ≤ g)
    (hsum : 1 ≤ ∑ i, e i) :
    (2 : ℝ) ^ (∑ i, e i) * (3 * ∑ i, (e i : ℝ) + 8) + 4
      ≤ 8 * ((∏ i, lenOf e g i : ℕ) : ℝ) * (Nat.log 2 (∏ i, lenOf e g i) : ℕ) := by
  have h := powerOfTwo_contract_bound_nat e g hg hsum
  exact_mod_cast h

end Contract

end IntegerMultBounds.NLogN
