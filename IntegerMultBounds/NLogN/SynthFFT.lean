import IntegerMultBounds.NLogN.NormFFT
import IntegerMultBounds.NLogN.FixedOps

/-! The synthetic FFT of Harvey and van der Hoeven, Lemma 3.2, in coefficient
form. Elements of `ℂ[y]/(y^r + 1)` are coefficient vectors `Fin r → ℂ` with the
sup norm, and multiplication by `y^e` is the signed cyclic shift `shiftNegZ e`,
an isometry with the semigroup law `y^a y^b = y^(a+b)`, period `2r`, and
`y^r = -1`. The normalised radix-2 recursion `fftNorm` with shift twiddles
computes the synthetic transform `(1/t) ∑ y^((2r/t) j k) u_k` exactly, for every
power of two `t ∣ 2r`, and the perturbed recursion deviates by at most `n ε`
after `n` levels: synthetic twiddles cost no rounding. The transform here uses
the `+` exponent; the paper's `G_t` is the same map with `y^(-…)`, i.e. the
transform at the inverse root. The identification of `shiftNegZ` with
multiplication in the quotient ring of `Synthetic.lean` is not made. -/

namespace IntegerMultBounds.NLogN

open Complex

section Shift

variable {r : ℕ} [NeZero r]

/-- Matrix entry `(j, i)` of multiplication by `y^e`: coefficient `j` lands at
index `(j + e) mod r` with sign `(-1)^((j + e) / r)`. -/
def shiftCoef (r e : ℕ) (j i : Fin r) : ℂ :=
  if (j.val + e) % r = i.val then (-1 : ℂ) ^ ((j.val + e) / r) else 0

/-- Multiplication by `y^e` on coefficient vectors. -/
def shiftNegZ (e : ℕ) (a : Fin r → ℂ) : Fin r → ℂ :=
  fun i => ∑ j, shiftCoef r e j i * a j

/-- The unique source index feeding output `i` under a shift by `e`. -/
def shiftSrc (r : ℕ) [NeZero r] (e : ℕ) (i : Fin r) : Fin r :=
  ⟨(i.val + (r - e % r)) % r, Nat.mod_lt _ (NeZero.pos r)⟩

theorem shiftSrc_spec (e : ℕ) (i : Fin r) : ((shiftSrc r e i).val + e) % r = i.val := by
  have hr := NeZero.pos r
  have hlt : e % r < r := Nat.mod_lt _ hr
  have hm := Nat.mod_add_div e r
  simp only [shiftSrc]
  rw [Nat.mod_add_mod]
  have h1 : i.val + (r - e % r) + e = i.val + r + r * (e / r) := by
    have h := Nat.sub_add_cancel hlt.le
    generalize r * (e / r) = q at hm ⊢
    omega
  rw [h1, Nat.add_mul_mod_self_left, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

theorem eq_shiftSrc_of {e : ℕ} {i : Fin r} {x : ℕ} (hx : x < r) (h : (x + e) % r = i.val) :
    x = (shiftSrc r e i).val := by
  have hs := shiftSrc_spec e i
  have hmod : x ≡ (shiftSrc r e i).val [MOD r] :=
    Nat.ModEq.add_right_cancel' e (by unfold Nat.ModEq; rw [h, hs])
  unfold Nat.ModEq at hmod
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (shiftSrc r e i).isLt] at hmod

theorem shiftCoef_src (e : ℕ) (i : Fin r) :
    shiftCoef r e (shiftSrc r e i) i = (-1 : ℂ) ^ (((shiftSrc r e i).val + e) / r) := by
  simp [shiftCoef, shiftSrc_spec]

theorem shiftCoef_eq_zero {e : ℕ} {i j : Fin r} (h : j ≠ shiftSrc r e i) :
    shiftCoef r e j i = 0 := by
  unfold shiftCoef
  split_ifs with hc
  · exact absurd (Fin.ext (eq_shiftSrc_of j.isLt hc)) h
  · rfl

/-- Closed form: one signed coefficient of the input. -/
theorem shiftNegZ_apply (e : ℕ) (a : Fin r → ℂ) (i : Fin r) :
    shiftNegZ e a i = (-1 : ℂ) ^ (((shiftSrc r e i).val + e) / r) * a (shiftSrc r e i) := by
  unfold shiftNegZ
  rw [Finset.sum_eq_single (shiftSrc r e i)]
  · rw [shiftCoef_src]
  · intro j _ hj
    rw [shiftCoef_eq_zero hj, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem norm_shiftNegZ_le (e : ℕ) (a : Fin r → ℂ) : ‖shiftNegZ e a‖ ≤ ‖a‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  rw [shiftNegZ_apply, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact norm_le_pi_norm a _

/-- The matrix of `y^(e₁)` times the matrix of `y^(e₂)` is the matrix of `y^(e₁ + e₂)`. -/
theorem shiftCoef_mul_sum (e₁ e₂ : ℕ) (j i : Fin r) :
    ∑ j', shiftCoef r e₁ j' i * shiftCoef r e₂ j j' = shiftCoef r (e₁ + e₂) j i := by
  have hr := NeZero.pos r
  rw [Finset.sum_eq_single (shiftSrc r e₁ i)]
  · rw [shiftCoef_src]
    unfold shiftCoef
    have hs := shiftSrc_spec e₁ i
    by_cases hc : (j.val + e₂) % r = (shiftSrc r e₁ i).val
    · have hi : (j.val + (e₁ + e₂)) % r = i.val := by
        rw [← hs, ← hc, Nat.mod_add_mod]
        congr 1; ring
      rw [ite_eq_left hc, ite_eq_left hi, ← pow_add]
      congr 1
      rw [← hc]
      have hd := Nat.mod_add_div (j.val + e₂) r
      calc ((j.val + e₂) % r + e₁) / r + (j.val + e₂) / r
          = ((j.val + e₂) % r + e₁ + r * ((j.val + e₂) / r)) / r := by
            rw [Nat.add_mul_div_left _ _ hr]
        _ = (j.val + (e₁ + e₂)) / r := by
            congr 1
            generalize r * ((j.val + e₂) / r) = q at hd ⊢
            omega
    · have hi : ¬ (j.val + (e₁ + e₂)) % r = i.val := by
        intro hi
        apply hc
        apply eq_shiftSrc_of (Nat.mod_lt _ hr)
        rw [Nat.mod_add_mod, ← hi]
        congr 1; ring
      rw [ite_eq_right hc, ite_eq_right hi, mul_zero]
  · intro j' _ hj'
    rw [shiftCoef_eq_zero hj', zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The semigroup law `y^(e₁) (y^(e₂) a) = y^(e₁ + e₂) a`. -/
theorem shiftNegZ_add (e₁ e₂ : ℕ) (a : Fin r → ℂ) :
    shiftNegZ e₁ (shiftNegZ e₂ a) = shiftNegZ (e₁ + e₂) a := by
  funext i
  unfold shiftNegZ
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← shiftCoef_mul_sum e₁ e₂ j i, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j' _
  ring

theorem shiftNegZ_zero (a : Fin r → ℂ) : shiftNegZ 0 a = a := by
  funext i
  rw [shiftNegZ_apply]
  have hsrc : shiftSrc r 0 i = i := by
    apply Fin.ext
    simp only [shiftSrc, Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt i.isLt
  rw [hsrc, Nat.add_zero, Nat.div_eq_of_lt i.isLt, pow_zero, one_mul]

theorem shiftSrc_mul (q : ℕ) (i : Fin r) : shiftSrc r (r * q) i = i := by
  apply Fin.ext
  simp only [shiftSrc, Nat.mul_mod_right, Nat.sub_zero, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt i.isLt

/-- `y^r = -1`. -/
theorem shiftNegZ_r (a : Fin r → ℂ) : shiftNegZ r a = -a := by
  funext i
  have h := shiftSrc_mul 1 i
  rw [mul_one] at h
  rw [shiftNegZ_apply, h, Nat.add_div_right _ (NeZero.pos r), Nat.div_eq_of_lt i.isLt]
  simp

/-- `y^(2r) = 1`. -/
theorem shiftNegZ_two_r (a : Fin r → ℂ) : shiftNegZ (2 * r) a = a := by
  funext i
  have h := shiftSrc_mul 2 i
  rw [mul_comm] at h
  rw [shiftNegZ_apply, h, show i.val + 2 * r = i.val + r * 2 by ring,
    Nat.add_mul_div_left _ _ (NeZero.pos r), Nat.div_eq_of_lt i.isLt]
  simp

theorem shiftNegZ_add_two_r_mul (e q : ℕ) (a : Fin r → ℂ) :
    shiftNegZ (e + 2 * r * q) a = shiftNegZ e a := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show e + 2 * r * (q + 1) = (e + 2 * r * q) + 2 * r by ring, ← shiftNegZ_add,
      shiftNegZ_two_r, ih]

theorem shiftNegZ_mod (e : ℕ) (a : Fin r → ℂ) : shiftNegZ e a = shiftNegZ (e % (2 * r)) a := by
  conv_lhs => rw [← Nat.mod_add_div e (2 * r)]
  exact shiftNegZ_add_two_r_mul _ _ a

/-- For `e < r` the shift is `shiftNeg` of `FixedOps.lean`, with the same signs. -/
theorem shiftNegZ_eq_shiftNeg {e : ℕ} (he : e < r) (a : Fin r → ℂ) :
    shiftNegZ e a = shiftNeg ⟨e, he⟩ a := by
  funext i
  rw [shiftNegZ_apply]
  unfold shiftNeg negaSign
  have hsub : (i - ⟨e, he⟩ : Fin r).val = (i.val + (r - e)) % r := by
    rw [Fin.val_sub, Fin.val_mk]; congr 1; omega
  have hsrc : (shiftSrc r e i).val = (i.val + (r - e)) % r := by
    simp only [shiftSrc, Nat.mod_eq_of_lt he]
  have hi := i.isLt
  by_cases hle : (⟨e, he⟩ : Fin r) ≤ i
  · rw [ite_eq_left hle]
    have hle' : e ≤ i.val := hle
    have hval : (i.val + (r - e)) % r = i.val - e := by
      rw [show i.val + (r - e) = (i.val - e) + r by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    have hsrc' : shiftSrc r e i = i - ⟨e, he⟩ := Fin.ext (by rw [hsrc, hsub])
    rw [hsrc', hsub, hval, show i.val - e + e = i.val by omega, Nat.div_eq_of_lt hi, pow_zero,
      one_mul]
  · rw [ite_eq_right hle]
    have hlt : i.val < e := by
      rw [Fin.le_def, Fin.val_mk] at hle; omega
    have hval : (i.val + (r - e)) % r = i.val + (r - e) := Nat.mod_eq_of_lt (by omega)
    have hsrc' : shiftSrc r e i = i - ⟨e, he⟩ := Fin.ext (by rw [hsrc, hsub])
    rw [hsrc', hsub, hval, show i.val + (r - e) + e = i.val + r by omega,
      Nat.add_div_right _ (NeZero.pos r), Nat.div_eq_of_lt hi]
    simp

/-- Multiplication by `y^e` as a continuous linear map. -/
noncomputable def shiftZCLM (r : ℕ) [NeZero r] (e : ℕ) : (Fin r → ℂ) →L[ℂ] (Fin r → ℂ) :=
  ContinuousLinearMap.pi fun i => ∑ j, shiftCoef r e j i • ContinuousLinearMap.proj j

theorem shiftZCLM_apply (e : ℕ) (a : Fin r → ℂ) : shiftZCLM r e a = shiftNegZ e a := by
  funext i
  simp [shiftZCLM, shiftNegZ, ContinuousLinearMap.pi_apply, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem opNorm_shiftZCLM_le (e : ℕ) : ‖shiftZCLM r e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  rw [shiftZCLM_apply, one_mul]
  exact norm_shiftNegZ_le e a

/-- The shift of `FixedOps.lean` as a continuous linear map. -/
noncomputable def shiftCLM (k : Fin r) : (Fin r → ℂ) →L[ℂ] (Fin r → ℂ) :=
  shiftZCLM r k.val

theorem shiftCLM_apply (k : Fin r) (a : Fin r → ℂ) : shiftCLM k a = shiftNeg k a := by
  rw [shiftCLM, shiftZCLM_apply, shiftNegZ_eq_shiftNeg k.isLt]

theorem opNorm_shiftCLM_le (k : Fin r) : ‖shiftCLM k‖ ≤ 1 :=
  opNorm_shiftZCLM_le k.val

end Shift

section Transform

variable {r : ℕ} [NeZero r]

/-- The synthetic transform of length `t ∣ 2r` at the root `y^(2r/t)`,
normalised by `1/t`. -/
noncomputable def synthDFT (r t : ℕ) (u : Fin t → (Fin r → ℂ)) : Fin t → (Fin r → ℂ) :=
  fun j => (1 / (t : ℂ)) • ∑ k, shiftNegZ ((2 * r / t) * j.val * k.val) (u k)

/-- Twiddles for the recursion at length `2^n`: depth `m` below the top uses
the root `y^((2r/2^n) 2^m)`. -/
noncomputable def wSynth (r : ℕ) [NeZero r] (n m k : ℕ) : (Fin r → ℂ) →L[ℂ] (Fin r → ℂ) :=
  shiftZCLM r ((2 * r / 2 ^ n) * 2 ^ m * k)

theorem norm_wSynth_le (n m k : ℕ) : ‖wSynth r n m k‖ ≤ 1 :=
  opNorm_shiftZCLM_le _

omit [NeZero r] in
theorem two_r_div_succ {n : ℕ} (h : 2 ^ (n + 1) ∣ 2 * r) :
    2 * r / 2 ^ n = 2 * (2 * r / 2 ^ (n + 1)) := by
  obtain ⟨q, hq⟩ := h
  rw [hq, Nat.mul_div_cancel_left q (by positivity : 0 < 2 ^ (n + 1)), pow_succ, mul_assoc,
    Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ n)]

theorem wSynth_succ {n : ℕ} (h : 2 ^ (n + 1) ∣ 2 * r) :
    (fun m => wSynth r (n + 1) (m + 1)) = wSynth r n := by
  funext m k
  unfold wSynth
  congr 1
  rw [two_r_div_succ h, pow_succ]
  ring

/-- Reduction of the top-level twiddle exponent on even positions. -/
theorem shiftNegZ_even {n : ℕ} (h : 2 ^ (n + 1) ∣ 2 * r) (i k : ℕ) (v : Fin r → ℂ) :
    shiftNegZ ((2 * r / 2 ^ (n + 1)) * k * (2 * i)) v
      = shiftNegZ ((2 * r / 2 ^ n) * (k % 2 ^ n) * i) v := by
  rw [two_r_div_succ h]
  obtain ⟨q, hq⟩ := h
  have hqq : 2 * r / 2 ^ (n + 1) = q := by
    rw [hq, Nat.mul_div_cancel_left _ (by positivity)]
  rw [hqq]
  have hk := Nat.mod_add_div k (2 ^ n)
  set m := k % 2 ^ n with hm
  set d := k / 2 ^ n with hd
  rw [show q * k * (2 * i) = 2 * q * m * i + 2 * r * (d * i) by
    rw [← hk, hq, pow_succ]; ring]
  exact shiftNegZ_add_two_r_mul _ _ v

/-- The normalised recursion with shift twiddles is the synthetic transform. -/
theorem fftNorm_synth : ∀ (n : ℕ), 2 ^ n ∣ 2 * r → ∀ u : Fin (2 ^ n) → (Fin r → ℂ),
    fftNorm n (wSynth r n) u = synthDFT r (2 ^ n) u
  | 0, _, u => by
    funext k
    have hval : ∀ j : Fin (2 ^ 0), j.val = 0 := fun j => by
      have := j.isLt
      have h : (2 : ℕ) ^ 0 = 1 := pow_zero 2
      omega
    have hk : ∀ j : Fin (2 ^ 0), j = k := fun j => Fin.ext (by rw [hval j, hval k])
    simp only [fftNorm, synthDFT]
    rw [Finset.sum_eq_single k (fun j _ hj => absurd (hk j) hj)
      (fun h => absurd (Finset.mem_univ k) h)]
    rw [hval k]
    simp [shiftNegZ_zero]
  | n + 1, hr, u => by
    funext k
    have h2 : 2 ^ n ∣ 2 * r := dvd_trans (pow_dvd_pow 2 (Nat.le_succ n)) hr
    simp only [fftNorm]
    rw [wSynth_succ hr, fftNorm_synth n h2, fftNorm_synth n h2]
    simp only [synthDFT, half]
    rw [← Fintype.sum_equiv (evenOddEquiv n)
      (fun j => shiftNegZ ((2 * r / 2 ^ (n + 1)) * k.val * (evenOddEquiv n j).val)
        (u (evenOddEquiv n j))) _ (fun _ => rfl)]
    rw [Fintype.sum_sum_type]
    have heven : ∀ i : Fin (2 ^ n),
        shiftNegZ ((2 * r / 2 ^ (n + 1)) * k.val * (evenOddEquiv n (Sum.inl i)).val)
          (u (evenOddEquiv n (Sum.inl i)))
        = shiftNegZ ((2 * r / 2 ^ n) * (k.val % 2 ^ n) * i.val) (u (evenOddEquiv n (Sum.inl i))) := by
      intro i
      have hv : (evenOddEquiv n (Sum.inl i)).val = 2 * i.val := rfl
      rw [hv, shiftNegZ_even hr]
    have hodd : ∀ i : Fin (2 ^ n),
        shiftNegZ ((2 * r / 2 ^ (n + 1)) * k.val * (evenOddEquiv n (Sum.inr i)).val)
          (u (evenOddEquiv n (Sum.inr i)))
        = shiftNegZ ((2 * r / 2 ^ (n + 1)) * k.val)
          (shiftNegZ ((2 * r / 2 ^ n) * (k.val % 2 ^ n) * i.val) (u (evenOddEquiv n (Sum.inr i)))) := by
      intro i
      have hv : (evenOddEquiv n (Sum.inr i)).val = 2 * i.val + 1 := rfl
      have h := shiftNegZ_even hr i k.val (u (evenOddEquiv n (Sum.inr i)))
      rw [hv, ← h, shiftNegZ_add]
      congr 1; ring
    rw [Finset.sum_congr rfl (fun i _ => heven i), Finset.sum_congr rfl (fun i _ => hodd i)]
    simp only [← shiftZCLM_apply]
    simp only [wSynth, pow_zero, mul_one, map_smul, map_sum, smul_add, smul_smul]
    rw [← smul_add]
    push_cast
    rw [pow_succ (2 : ℂ) n]
    field_simp
    rw [smul_add]

/-- The synthetic transform is a contraction in the sup norm. -/
theorem norm_synthDFT_le {n : ℕ} (hr : 2 ^ n ∣ 2 * r) {A : ℝ} {u : Fin (2 ^ n) → (Fin r → ℂ)}
    (hA : ∀ j, ‖u j‖ ≤ A) (k : Fin (2 ^ n)) : ‖synthDFT r (2 ^ n) u k‖ ≤ A := by
  rw [← fftNorm_synth n hr]
  exact fftNorm_bound n _ (fun m k => norm_wSynth_le n m k) A u hA k

/-- Lemma 3.2 for the synthetic ring: with exact shift twiddles and additive
error at most `ε` per level, the computed transform is within `n ε`. -/
theorem synth_fft_err {n : ℕ} (hr : 2 ^ n ∣ 2 * r) {ε : ℝ}
    {e : (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)} (hε : ∀ m k, ‖e m k‖ ≤ ε)
    (u : Fin (2 ^ n) → (Fin r → ℂ)) (k : Fin (2 ^ n)) :
    ‖fftNormErr n (wSynth r n) e u k - synthDFT r (2 ^ n) u k‖ ≤ n * ε := by
  rw [← fftNorm_synth n hr]
  exact fftNormErr_sub_fftNorm n _ (fun m k => norm_wSynth_le n m k) ε e hε u k

end Transform

end IntegerMultBounds.NLogN
