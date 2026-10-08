import IntegerMultBounds.NLogN.SynthFFT

/-! The convolution theorem and inversion for the synthetic transform in
coefficient form, the analogue of (2.1) and Lemma 2.3 of Harvey and van der
Hoeven for `R = ℂ[y]/(y^r + 1)`. The negacyclic product of `FixedOps.lean` is
the sum `∑ a_i y^i b` of signed shifts, hence bilinear, associative, unital,
and compatible with shifts. A cyclic convolution of vectors with `R`
coefficients has synthetic transform equal to `t` times the pointwise
negacyclic product of the transforms, and for a power of two `t ∣ 2r` the
transform at the inverse root `y^((2r/t)(t-1))` recovers `u/t`. Orthogonality
`∑_k y^((2r/t) m k) = 0` for `0 < m < t` is proved from `y^r = -1` alone. Fixed
point errors of this pipeline are not treated here. -/

namespace IntegerMultBounds.NLogN

section Algebra

variable {r : ℕ} [NeZero r]

theorem shiftNegZ_add_vec (e : ℕ) (a b : Fin r → ℂ) :
    shiftNegZ e (a + b) = shiftNegZ e a + shiftNegZ e b := by
  rw [← shiftZCLM_apply, ← shiftZCLM_apply, ← shiftZCLM_apply, map_add]

theorem shiftNegZ_smul (e : ℕ) (c : ℂ) (a : Fin r → ℂ) :
    shiftNegZ e (c • a) = c • shiftNegZ e a := by
  rw [← shiftZCLM_apply, ← shiftZCLM_apply, map_smul]

theorem shiftNegZ_neg (e : ℕ) (a : Fin r → ℂ) : shiftNegZ e (-a) = -shiftNegZ e a := by
  rw [← shiftZCLM_apply, ← shiftZCLM_apply, map_neg]

theorem shiftNegZ_sum {ι : Type*} (e : ℕ) (s : Finset ι) (f : ι → Fin r → ℂ) :
    shiftNegZ e (∑ i ∈ s, f i) = ∑ i ∈ s, shiftNegZ e (f i) := by
  rw [← shiftZCLM_apply, map_sum]
  simp only [shiftZCLM_apply]

/-- The negacyclic product is the sum of the signed shifts `a_i y^i b`. -/
theorem negacyclicMul_eq_sum_shift (a b : Fin r → ℂ) :
    negacyclicMul a b = ∑ i, a i • shiftNegZ i.val b := by
  funext k
  simp only [negacyclicMul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  have h := shiftNegZ_eq_shiftNeg i.isLt b
  simp only [Fin.eta] at h
  rw [h]
  simp only [shiftNeg, negaIdx]
  ring

theorem negacyclicMul_eq_sum_shift' (a b : Fin r → ℂ) :
    negacyclicMul a b = ∑ i, b i • shiftNegZ i.val a := by
  rw [negacyclicMul_comm, negacyclicMul_eq_sum_shift]

theorem negacyclicMul_add_left (a a' b : Fin r → ℂ) :
    negacyclicMul (a + a') b = negacyclicMul a b + negacyclicMul a' b := by
  simp only [negacyclicMul_eq_sum_shift, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem negacyclicMul_add_right (a b b' : Fin r → ℂ) :
    negacyclicMul a (b + b') = negacyclicMul a b + negacyclicMul a b' := by
  simp only [negacyclicMul_eq_sum_shift', Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem negacyclicMul_smul_left (c : ℂ) (a b : Fin r → ℂ) :
    negacyclicMul (c • a) b = c • negacyclicMul a b := by
  simp only [negacyclicMul_eq_sum_shift, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem negacyclicMul_smul_right (c : ℂ) (a b : Fin r → ℂ) :
    negacyclicMul a (c • b) = c • negacyclicMul a b := by
  simp only [negacyclicMul_eq_sum_shift', Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem negacyclicMul_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ) (b : Fin r → ℂ) :
    negacyclicMul (∑ i ∈ s, f i) b = ∑ i ∈ s, negacyclicMul (f i) b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    simp [negacyclicMul_eq_sum_shift]
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, negacyclicMul_add_left, ih]

theorem negacyclicMul_sum_right {ι : Type*} (s : Finset ι) (a : Fin r → ℂ) (f : ι → Fin r → ℂ) :
    negacyclicMul a (∑ i ∈ s, f i) = ∑ i ∈ s, negacyclicMul a (f i) := by
  rw [negacyclicMul_comm, negacyclicMul_sum_left]
  simp only [negacyclicMul_comm a]

/-- Multiplication by `y^e` commutes with the ring product. -/
theorem shiftNegZ_negacyclicMul (e : ℕ) (a b : Fin r → ℂ) :
    shiftNegZ e (negacyclicMul a b) = negacyclicMul (shiftNegZ e a) b := by
  rw [negacyclicMul_eq_sum_shift', negacyclicMul_eq_sum_shift', shiftNegZ_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [shiftNegZ_smul, shiftNegZ_add, shiftNegZ_add, Nat.add_comm]

theorem negacyclicMul_assoc (a b c : Fin r → ℂ) :
    negacyclicMul (negacyclicMul a b) c = negacyclicMul a (negacyclicMul b c) := by
  rw [negacyclicMul_eq_sum_shift' (negacyclicMul a b) c, negacyclicMul_eq_sum_shift a b,
    negacyclicMul_eq_sum_shift a (negacyclicMul b c), negacyclicMul_eq_sum_shift' b c]
  simp only [shiftNegZ_sum, shiftNegZ_smul, shiftNegZ_add, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_comm, Nat.add_comm]

/-- `1 = y^0` is the unit. -/
theorem negacyclicMul_single_zero_one (a : Fin r → ℂ) :
    negacyclicMul (Pi.single 0 1) a = a := by
  rw [negacyclicMul_eq_sum_shift]
  rw [Finset.sum_eq_single (0 : Fin r)]
  · simp [shiftNegZ_zero]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

end Algebra

section Convolution

variable {r : ℕ} [NeZero r]

/-- Cyclic convolution of vectors with coefficients in the synthetic ring. -/
def synthConv (t : ℕ) [NeZero t] (u v : Fin t → (Fin r → ℂ)) : Fin t → (Fin r → ℂ) :=
  fun k => ∑ i, negacyclicMul (u i) (v (k - i))

/-- Exponents may be reduced modulo `t` when `(2r/t) t = 2r`. -/
theorem shiftNegZ_mul_mod {t : ℕ} (hr : t ∣ 2 * r) (k M : ℕ) (x : Fin r → ℂ) :
    shiftNegZ ((2 * r / t) * k * M) x = shiftNegZ ((2 * r / t) * k * (M % t)) x := by
  have hct : 2 * r / t * t = 2 * r := Nat.div_mul_cancel hr
  conv_lhs => rw [← Nat.mod_add_div M t]
  have h : 2 * r / t * k * (M % t + t * (M / t))
      = 2 * r / t * k * (M % t) + (2 * r / t * t) * (k * (M / t)) := by ring
  rw [h, hct]
  exact shiftNegZ_add_two_r_mul _ _ x

theorem shiftNegZ_mul_val_add {t : ℕ} [NeZero t] (hr : t ∣ 2 * r) (j : ℕ) (i m : Fin t)
    (x : Fin r → ℂ) :
    shiftNegZ ((2 * r / t) * j * (i + m).val) x
      = shiftNegZ ((2 * r / t) * j * (i.val + m.val)) x := by
  rw [Fin.val_add, ← shiftNegZ_mul_mod hr]

/-- The convolution theorem: the transform of a convolution is `t` times the
pointwise negacyclic product of the transforms. -/
theorem synthDFT_conv {t : ℕ} [NeZero t] (hr : t ∣ 2 * r) (u v : Fin t → (Fin r → ℂ)) :
    synthDFT r t (synthConv t u v)
      = fun j => (t : ℂ) • negacyclicMul (synthDFT r t u j) (synthDFT r t v j) := by
  funext j
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  have key : ∑ k, shiftNegZ ((2 * r / t) * j.val * k.val) (synthConv t u v k)
      = ∑ i, ∑ m, negacyclicMul (shiftNegZ ((2 * r / t) * j.val * i.val) (u i))
          (shiftNegZ ((2 * r / t) * j.val * m.val) (v m)) := by
    simp only [synthConv, shiftNegZ_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Fintype.sum_equiv (Equiv.addLeft i)
      (fun m => shiftNegZ ((2 * r / t) * j.val * (i + m).val)
        (negacyclicMul (u i) (v (i + m - i))))
      (fun k => shiftNegZ ((2 * r / t) * j.val * k.val) (negacyclicMul (u i) (v (k - i))))
      (fun m => rfl)]
    apply Finset.sum_congr rfl
    intro m _
    rw [add_sub_cancel_left, shiftNegZ_mul_val_add hr, mul_add, Nat.add_comm, ← shiftNegZ_add,
      shiftNegZ_negacyclicMul, negacyclicMul_comm, shiftNegZ_negacyclicMul, negacyclicMul_comm]
  simp only [synthDFT]
  rw [key, negacyclicMul_smul_left, negacyclicMul_smul_right, smul_smul, smul_smul,
    negacyclicMul_sum_left]
  simp only [negacyclicMul_sum_right]
  congr 1
  field_simp

end Convolution

section Inversion

variable {r : ℕ} [NeZero r]

omit [NeZero r] in
/-- A sequence with `f (k + n) = -f k` sums to zero over any block of length `2n`. -/
theorem sum_range_two_mul_eq_zero {V : Type*} [AddCommGroup V] (f : ℕ → V) (n : ℕ)
    (hf : ∀ k, f (k + n) = -f k) : ∑ k ∈ Finset.range (2 * n), f k = 0 := by
  rw [two_mul, Finset.sum_range_add]
  have : ∑ x ∈ Finset.range n, f (n + x) = -∑ x ∈ Finset.range n, f x := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [Nat.add_comm, hf]
  rw [this, add_neg_cancel]

omit [NeZero r] in
theorem sum_range_mul_eq_zero_of_periodic {V : Type*} [AddCommGroup V] (f : ℕ → V)
    (n : ℕ) (hf : ∀ k, f (k + n) = f k) (h0 : ∑ k ∈ Finset.range n, f k = 0) (q : ℕ) :
    ∑ k ∈ Finset.range (q * n), f k = 0 := by
  have hshift : ∀ q k, f (q * n + k) = f k := by
    intro q k
    induction q with
    | zero => simp
    | succ q ihq => rw [Nat.succ_mul, show q * n + n + k = (q * n + k) + n by ring, hf, ihq]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, zero_add]
    rw [Finset.sum_congr rfl (fun k _ => hshift q k), h0]

/-- Orthogonality of the synthetic root of unity for a power-of-two length. -/
theorem sum_shiftNegZ_eq_zero {t f : ℕ} (hr : t ∣ 2 * r) (ht : t = 2 ^ f) {m : ℕ}
    (hm : 0 < m) (hmt : m < t) (a : Fin r → ℂ) :
    ∑ k : Fin t, shiftNegZ ((2 * r / t) * m * k.val) a = 0 := by
  have hct : 2 * r / t * t = 2 * r := Nat.div_mul_cancel hr
  obtain ⟨e, m', hm', hme⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' 2 (by norm_num)
  -- `e < f` since `2^e ≤ m < 2^f`
  have hef : e < f := by
    by_contra h
    push Not at h
    have : 2 ^ f ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h
    have hm'pos : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hme; omega)
    have : 2 ^ e ≤ m := by rw [hme]; exact Nat.le_mul_of_pos_right _ hm'pos
    omega
  obtain ⟨m'', hm''⟩ : ∃ m'', m' = 2 * m'' + 1 := by
    rcases Nat.even_or_odd m' with h | h
    · exact absurd (even_iff_two_dvd.mp h) hm'
    · exact h
  set c := 2 * r / t with hc
  set n := 2 ^ (f - e - 1) with hn
  -- `c * 2^(f-1) = r`
  have hhalf : c * 2 ^ (f - 1) = r := by
    have hf1 : f = (f - 1) + 1 := by omega
    have : c * 2 ^ f = 2 * r := by rw [← ht]; exact hct
    rw [hf1, pow_succ, ← mul_assoc] at this
    omega
  have hcmn : c * m * n = r * m' := by
    rw [hme, hn, ← hhalf, show f - 1 = e + (f - e - 1) by omega, pow_add]
    ring
  have hblock : ∀ k, shiftNegZ (c * m * (k + n)) a = -shiftNegZ (c * m * k) a := by
    intro k
    rw [mul_add, ← shiftNegZ_add, hcmn, hm'', show r * (2 * m'' + 1) = r + 2 * r * m'' by ring,
      shiftNegZ_add_two_r_mul, shiftNegZ_r, shiftNegZ_neg]
  have hper : ∀ k, shiftNegZ (c * m * (k + 2 * n)) a = shiftNegZ (c * m * k) a := by
    intro k
    have h2 : c * m * (k + 2 * n) = c * m * k + 2 * (c * m * n) := by ring
    rw [h2, hcmn, ← mul_assoc]
    exact shiftNegZ_add_two_r_mul _ _ a
  have hzero : ∑ k ∈ Finset.range (2 * n), shiftNegZ (c * m * k) a = 0 :=
    sum_range_two_mul_eq_zero (fun k => shiftNegZ (c * m * k) a) n hblock
  have htn : t = 2 ^ e * (2 * n) := by
    rw [ht, hn]
    obtain ⟨g, hg⟩ : ∃ g, f = e + 1 + g := ⟨f - e - 1, by omega⟩
    rw [hg, show e + 1 + g - e - 1 = g by omega, pow_add, pow_succ]; ring
  rw [Fin.sum_univ_eq_sum_range (fun k => shiftNegZ (c * m * k) a) t, htn]
  exact sum_range_mul_eq_zero_of_periodic (fun k => shiftNegZ (c * m * k) a) (2 * n) hper hzero _

/-- The transform at the inverse root `y^((2r/t)(t-1))`, normalised by `1/t`. -/
noncomputable def synthDFTInv (r t : ℕ) (u : Fin t → (Fin r → ℂ)) : Fin t → (Fin r → ℂ) :=
  fun j => (1 / (t : ℂ)) • ∑ k, shiftNegZ ((2 * r / t) * (t - 1) * j.val * k.val) (u k)

/-- Inversion: `F_{ω⁻¹} F_ω u = u / t` for a power-of-two length `t ∣ 2r`. -/
theorem synthDFTInv_synthDFT {t f : ℕ} [NeZero t] (hr : t ∣ 2 * r) (ht : t = 2 ^ f)
    (u : Fin t → (Fin r → ℂ)) :
    synthDFTInv r t (synthDFT r t u) = fun j => (1 / (t : ℂ)) • u j := by
  funext j
  have htpos : 0 < t := NeZero.pos t
  simp only [synthDFTInv, synthDFT, shiftNegZ_sum, shiftNegZ_smul, Finset.smul_sum, smul_smul,
    shiftNegZ_add]
  rw [Finset.sum_comm]
  have hterm : ∀ i : Fin t, ∑ k : Fin t,
      (1 / (t : ℂ) * (1 / (t : ℂ))) •
        shiftNegZ ((2 * r / t) * (t - 1) * j.val * k.val + (2 * r / t) * k.val * i.val) (u i)
      = if i = j then (1 / (t : ℂ)) • u j else 0 := by
    intro i
    have hexp : ∀ k : Fin t, (2 * r / t) * (t - 1) * j.val * k.val + (2 * r / t) * k.val * i.val
        = (2 * r / t) * k.val * ((t - 1) * j.val + i.val) := fun k => by ring
    simp only [hexp]
    by_cases hij : i = j
    · subst hij
      have hred : ∀ k : Fin t, shiftNegZ ((2 * r / t) * k.val * ((t - 1) * i.val + i.val)) (u i)
          = u i := by
        intro k
        have hle := Nat.le_mul_of_pos_left i.val htpos
        rw [shiftNegZ_mul_mod hr, show (t - 1) * i.val + i.val = t * i.val by
          rw [Nat.sub_one_mul]; omega]
        rw [Nat.mul_mod_right, mul_zero, shiftNegZ_zero]
      simp only [hred, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← smul_assoc,
        nsmul_eq_mul]
      congr 1
      have ht' : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr htpos.ne'
      field_simp
    · rw [ite_eq_right hij, ← Finset.smul_sum]
      set M := (t - 1) * j.val + i.val with hM
      have hMmod : 0 < M % t ∧ M % t < t := by
        refine ⟨?_, Nat.mod_lt _ htpos⟩
        have hi := i.isLt
        have hj := j.isLt
        have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
        rw [hM, Nat.sub_one_mul]
        by_contra h0
        push Not at h0
        have hdvd : t ∣ t * j.val - j.val + i.val := Nat.dvd_of_mod_eq_zero (by omega)
        have hge : t * j.val - j.val + i.val + j.val = t * j.val + i.val := by
          have := Nat.le_mul_of_pos_left j.val htpos
          omega
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · -- `t j - j + i = t (j - 1) + (t + i - j)` with `0 < t + i - j < t`
          obtain ⟨q, hq⟩ := hdvd
          have h1 : t * j.val - j.val + i.val = t * (j.val - 1) + (t + i.val - j.val) := by
            have := Nat.le_mul_of_pos_left j.val htpos
            rcases Nat.eq_zero_or_pos j.val with hj0 | hj0
            · omega
            · have := Nat.le_mul_of_pos_right t hj0
              rw [Nat.mul_sub_one]; omega
          rw [h1] at hq
          have hq1 : q ≤ j.val - 1 := by
            by_contra hq1
            push Not at hq1
            have : t * (j.val - 1) + t ≤ t * q := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hq1
            omega
          have hq2 : j.val - 1 < q := by
            by_contra hq2
            push Not at hq2
            have : t * q ≤ t * (j.val - 1) := Nat.mul_le_mul_left _ hq2
            omega
          omega
        · -- `t j - j + i = t j + (i - j)` with `0 < i - j < t`
          obtain ⟨q, hq⟩ := hdvd
          have h1 : t * j.val - j.val + i.val = t * j.val + (i.val - j.val) := by
            have := Nat.le_mul_of_pos_left j.val htpos
            omega
          rw [h1] at hq
          have hq1 : q ≤ j.val := by
            by_contra hq1
            push Not at hq1
            have : t * j.val + t ≤ t * q := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hq1
            omega
          have hq2 : j.val < q := by
            by_contra hq2
            push Not at hq2
            have : t * q ≤ t * j.val := Nat.mul_le_mul_left _ hq2
            omega
          omega
      have hred : ∀ k : Fin t, shiftNegZ ((2 * r / t) * k.val * M) (u i)
          = shiftNegZ ((2 * r / t) * (M % t) * k.val) (u i) := by
        intro k
        rw [shiftNegZ_mul_mod hr, mul_right_comm]
      simp only [hred]
      rw [sum_shiftNegZ_eq_zero hr ht hMmod.1 hMmod.2, smul_zero]
  simp only [hterm]
  rw [Finset.sum_ite_eq' Finset.univ j]
  simp

end Inversion

end IntegerMultBounds.NLogN
