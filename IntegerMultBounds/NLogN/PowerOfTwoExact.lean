import IntegerMultBounds.NLogN.SynthMultiD
import IntegerMultBounds.NLogN.BluesteinApprox
import IntegerMultBounds.NLogN.SynthConvApprox

/-! The exact algebraic chain behind Theorem 3.1 of Harvey and van der Hoeven
(Propositions 3.4 and 3.5): the normalized complex transform of power-of-two
sizes is a chirp multiplication, then the normalized complex cyclic convolution,
which after twisting the last coordinate is a convolution over the synthetic
ring, which the synthetic transform, pointwise negacyclic products, and the
inverse synthetic transform compute exactly. Proved: linearity of the
`d`-dimensional synthetic transforms and the `d`-dimensional pipeline identity
for the normalized synthetic convolution; the transport of the normalized
complex convolution on `G × Fin r` through the twist for any finite abelian
group `G`; the chirp identity on `Fin t`; and the complete chain for two
coordinates `Fin t × Fin r`, together with the identification of the
two-coordinate transform with `dft2`. Fixed-point errors are not treated
here, and the chain for more than two coordinates follows by the same
transport along `Fin.snoc` and is not written. -/

namespace IntegerMultBounds.NLogN

open Complex Real

section Linearity

variable {r : ℕ} [NeZero r] {d : ℕ} {N : Fin d → ℕ} [∀ i, NeZero (N i)]

omit [∀ i, NeZero (N i)] in
theorem synthDFTD_smul (c : ℂ) (u : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) :
    synthDFTD r N (fun j => c • u j) = fun j => c • synthDFTD r N u j := by
  funext j
  simp only [synthDFTD, shiftNegZ_smul, ← Finset.smul_sum, smul_comm c]

omit [∀ i, NeZero (N i)] in
theorem synthDFTDInv_smul (c : ℂ) (u : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) :
    synthDFTDInv r N (fun j => c • u j) = fun j => c • synthDFTDInv r N u j := by
  funext j
  simp only [synthDFTDInv, shiftNegZ_smul, ← Finset.smul_sum, smul_comm c]

/-- The `d`-dimensional pipeline identity: the normalized synthetic convolution
`(1/T) U ∗ V` is `T r` times the inverse transform of the `1/r`-scaled pointwise
negacyclic products of the forward transforms. -/
theorem synthConvNormD_eq (hN : ∀ i, N i ∣ 2 * r) (hpow : ∀ i, ∃ f, N i = 2 ^ f)
    (U V : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) :
    (fun j => (1 / ((∏ i, N i : ℕ) : ℂ)) • synthConvG U V j)
      = fun j => (((∏ i, N i : ℕ) : ℂ) * r) • synthDFTDInv r N
          (fun j => (1 / (r : ℂ)) • negacyclicMul (synthDFTD r N U j) (synthDFTD r N V j)) j := by
  have hinv := synthDFTDInv_synthDFTD hN hpow (synthConvG U V)
  rw [synthDFTD_conv hN] at hinv
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have h1 : (fun j => ((∏ i, N i : ℕ) : ℂ) •
      negacyclicMul (synthDFTD r N U j) (synthDFTD r N V j))
      = fun j => (((∏ i, N i : ℕ) : ℂ) * r) • ((1 / (r : ℂ)) •
        negacyclicMul (synthDFTD r N U j) (synthDFTD r N V j)) := by
    funext j
    rw [smul_smul]
    congr 1
    field_simp
  rw [h1, synthDFTDInv_smul] at hinv
  exact hinv.symm

/-- The one-dimensional pipeline identity at any power-of-two length `t ∣ 2r`. -/
theorem synthConvNormT_eq {t f : ℕ} [NeZero t] (hr : t ∣ 2 * r) (ht : t = 2 ^ f)
    (U V : Fin t → (Fin r → ℂ)) :
    (fun j => (1 / (t : ℂ)) • synthConv t U V j)
      = fun j => ((t : ℂ) * r) • synthDFTInv r t
          (fun j => (1 / (r : ℂ)) • negacyclicMul (synthDFT r t U j) (synthDFT r t V j)) j := by
  have hinv := synthDFTInv_synthDFT hr ht (synthConv t U V)
  rw [synthDFT_conv hr] at hinv
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have h1 : (fun j => (t : ℂ) • negacyclicMul (synthDFT r t U j) (synthDFT r t V j))
      = fun j => ((t : ℂ) * r) • ((1 / (r : ℂ)) •
        negacyclicMul (synthDFT r t U j) (synthDFT r t V j)) := by
    funext j
    rw [smul_smul]
    congr 1
    field_simp
  rw [h1, synthDFTInv_smul] at hinv
  exact hinv.symm

/-- The scaling used in the two-coordinate chain: `(1/(t r)) U ∗ V` is `t` times
the inverse transform of the scaled pointwise products. -/
theorem scaled_synthConv_eq {t f : ℕ} [NeZero t] (hr : t ∣ 2 * r) (ht : t = 2 ^ f)
    (U V : Fin t → (Fin r → ℂ)) :
    (fun j => (1 / ((t * r : ℕ) : ℂ)) • synthConv t U V j)
      = fun j => (t : ℂ) • synthDFTInv r t
          (fun j => (1 / (r : ℂ)) • negacyclicMul (synthDFT r t U j) (synthDFT r t V j)) j := by
  have h := synthConvNormT_eq hr ht U V
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have ht0 : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  funext j
  have hj := congrFun h j
  calc (1 / ((t * r : ℕ) : ℂ)) • synthConv t U V j
      = (1 / (r : ℂ)) • ((1 / (t : ℂ)) • synthConv t U V j) := by
        rw [smul_smul]
        congr 1
        push_cast
        field_simp
    _ = (1 / (r : ℂ)) • (((t : ℂ) * r) • synthDFTInv r t
          (fun j => (1 / (r : ℂ)) • negacyclicMul (synthDFT r t U j) (synthDFT r t V j)) j) := by
        rw [hj]
    _ = _ := by
        rw [smul_smul]
        congr 1
        field_simp

end Linearity

section Transport

variable {r : ℕ} [NeZero r] {G : Type*} [AddCommGroup G] [Fintype G]

omit [NeZero r] [AddCommGroup G] [Fintype G] in
theorem ofSynth_smul (c : ℂ) (w : G → (Fin r → ℂ)) :
    ofSynth (fun j => c • w j) = fun p => c * ofSynth w p := by
  funext p
  simp only [ofSynth, untwist, Pi.smul_apply, smul_eq_mul]
  ring

/-- The normalized complex convolution on `G × Fin r` is the untwist of the
normalized synthetic convolution of the twisted slices. -/
theorem convNorm_prod_eq (u v : G × Fin r → ℂ) :
    (fun p => (1 / ((Fintype.card G * r : ℕ) : ℂ)) * convG u v p)
      = ofSynth (fun j => (1 / ((Fintype.card G * r : ℕ) : ℂ)) •
          synthConvG (toSynth u) (toSynth v) j) := by
  rw [ofSynth_smul, ← convG_eq_ofSynth]

end Transport

section ChirpFin

variable {t : ℕ} [NeZero t]

/-- The chirp `e^{πi j²/t}` on `Fin t`. -/
noncomputable def chirpF (t : ℕ) (j : Fin t) : ℂ := chirpExp t ((j.val : ℤ) ^ 2)

omit [NeZero t] in
theorem norm_chirpF (j : Fin t) : ‖chirpF t j‖ = 1 := by
  unfold chirpF chirpExp
  have : (π : ℂ) * I * (((j.val : ℤ) ^ 2 : ℤ) : ℂ) / t
      = ((π * ((j.val : ℤ) ^ 2 : ℤ) / t : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- For even `t` the chirp at a `Fin` difference is the chirp of the integer
difference. -/
theorem chirpF_sub_eq (ht : 2 ∣ t) (j k : Fin t) :
    chirpF t (j - k) = chirpExp t (((j.val : ℤ) - k.val) ^ 2) := by
  unfold chirpF
  by_cases h : k ≤ j
  · have hv := Fin.coe_sub_iff_le.mpr h
    have hle : k.val ≤ j.val := Fin.le_iff_val_le_val.mp h
    congr 2
    rw [hv]
    omega
  · have hlt : j < k := not_le.mp h
    have hv := Fin.coe_sub_iff_lt.mpr hlt
    have hcast : (((j - k).val : ℕ) : ℤ) = ((j.val : ℤ) - k.val) + t * 1 := by
      rw [hv]
      omega
    rw [hcast]
    exact chirpExp_sq_add ht _ 1

/-- The chirp identity on `Fin t`: `a_{j−k} ā_j ā_k = e^{−2πi jk/t}`. -/
theorem chirpF_sub_mul (ht : 2 ∣ t) (j k : Fin t) :
    chirpF t (j - k) * (starRingEnd ℂ) (chirpF t j) * (starRingEnd ℂ) (chirpF t k) =
      Complex.exp (-2 * π * I * (j.val * k.val : ℕ) / t) := by
  rw [chirpF_sub_eq ht, chirpF, chirpF, chirpExp_conj, chirpExp_conj, chirpExp_mul, chirpExp_mul,
    exp_neg_two_eq]
  congr 1
  push_cast
  ring

end ChirpFin

section TwoCoordinates

variable {t r : ℕ} [NeZero t] [NeZero r]

/-- The normalized two-coordinate complex transform on `Fin t × Fin r`. -/
noncomputable def dftNorm2 (t r : ℕ) (u : Fin t × Fin r → ℂ) : Fin t × Fin r → ℂ :=
  fun k => (1 / ((t * r : ℕ) : ℂ)) * ∑ j,
    Complex.exp (-2 * π * I * (j.1.val * k.1.val : ℕ) / t) *
      Complex.exp (-2 * π * I * (j.2.val * k.2.val : ℕ) / r) * u j

/-- The two-coordinate chirp. -/
noncomputable def chirp2 (t r : ℕ) (j : Fin t × Fin r) : ℂ := chirpF t j.1 * chirpF r j.2

/-- The normalized two-coordinate convolution `(1/(t r)) a ∗ b`. -/
noncomputable def convNorm2 (t r : ℕ) [NeZero t] [NeZero r] (a b : Fin t × Fin r → ℂ) : Fin t × Fin r → ℂ :=
  fun k => (1 / ((t * r : ℕ) : ℂ)) * convG a b k

omit [NeZero t] [NeZero r] in
theorem norm_chirp2 (j : Fin t × Fin r) : ‖chirp2 t r j‖ = 1 := by
  simp only [chirp2, norm_mul, norm_chirpF, one_mul]

/-- Bluestein for two even coordinates. -/
theorem bluestein2 (ht : 2 ∣ t) (hr : 2 ∣ r) (u : Fin t × Fin r → ℂ) :
    dftNorm2 t r u = fun k => (starRingEnd ℂ) (chirp2 t r k) *
      convNorm2 t r (chirp2 t r) (fun j => (starRingEnd ℂ) (chirp2 t r j) * u j) k := by
  funext k
  simp only [dftNorm2, convNorm2]
  rw [convG_comm]
  simp only [convG, Finset.mul_sum, chirp2, map_mul, Prod.fst_sub, Prod.snd_sub]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := chirpF_sub_mul ht k.1 j.1
  have h2 := chirpF_sub_mul hr k.2 j.2
  rw [mul_comm k.1.val j.1.val] at h1
  rw [mul_comm k.2.val j.2.val] at h2
  rw [← h1, ← h2]
  ring

/-- The two-coordinate transform is `dft2` at the roots `e^{-2πi/t}`, `e^{-2πi/r}`,
normalized by `1/(t r)`, for positive lengths written as successors. -/
theorem dftNorm2_eq_dft2 {m m' : ℕ} (a : Fin (m + 1) × Fin (m' + 1) → ℂ) :
    dftNorm2 (m + 1) (m' + 1) a = fun k => (1 / (((m + 1) * (m' + 1) : ℕ) : ℂ)) *
      dft2 (m := m + 1) (n := m' + 1) (Complex.exp (-2 * π * I / ((m + 1 : ℕ) : ℂ)))
        (Complex.exp (-2 * π * I / ((m' + 1 : ℕ) : ℂ))) a k := by
  funext k
  simp only [dftNorm2, dft2]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [omega_pow_val (t := m + 1) j.1 k.1, omega_pow_val (t := m' + 1) j.2 k.2]
  rfl

/-- The exact chain of Theorem 3.1 for two coordinates: chirp, twist, synthetic
forward transforms, scaled negacyclic products, inverse synthetic transform,
untwist, chirp. -/
theorem dftNorm2_chain {f : ℕ} (ht2 : 2 ∣ t) (hr2 : 2 ∣ r) (htr : t ∣ 2 * r) (hpow : t = 2 ^ f)
    (u : Fin t × Fin r → ℂ) :
    dftNorm2 t r u = fun k => (starRingEnd ℂ) (chirp2 t r k) *
      ofSynth (fun j => (t : ℂ) • synthDFTInv r t
        (fun j => (1 / (r : ℂ)) • negacyclicMul (synthDFT r t (toSynth (chirp2 t r)) j)
          (synthDFT r t (toSynth (fun j => (starRingEnd ℂ) (chirp2 t r j) * u j)) j)) j) k := by
  rw [bluestein2 ht2 hr2]
  funext k
  congr 1
  have hc := congrFun (convNorm_prod_eq (G := Fin t) (chirp2 t r)
    (fun j => (starRingEnd ℂ) (chirp2 t r j) * u j)) k
  simp only [Fintype.card_fin] at hc
  show (1 / ((t * r : ℕ) : ℂ)) * convG _ _ k = _
  rw [hc, synthConvG_eq_synthConv, scaled_synthConv_eq htr hpow]

end TwoCoordinates

end IntegerMultBounds.NLogN
