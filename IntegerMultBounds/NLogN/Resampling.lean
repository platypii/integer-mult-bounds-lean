import IntegerMultBounds.NLogN.Gaussian
import IntegerMultBounds.NLogN.DFT
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Tactic

/-! Gaussian resampling, after Harvey and van der Hoeven, Section 4.1. The
normalised complex transform `dftC`, the resampling maps `resampS` and
`resampT`, and the permutations `permS`, `permT` are defined exactly as in the
paper. Proved: shifted Poisson summation for the Gaussian, derived from the
Jacobi theta functional equation; orthogonality of the additive characters;
and the resampling identity `T ∘ Ps ∘ Fs = Pt ∘ Ft ∘ S` for all positive
lengths. The left inverse of `T`, its norm bounds, and every fixed-point
approximation are not part of this file. -/

namespace IntegerMultBounds.NLogN

open Real Complex

/-- The additive character `x ↦ exp (2πix)` on `ℝ`. -/
noncomputable def chr (x : ℝ) : ℂ := Complex.exp (2 * π * I * x)

theorem chr_add (x y : ℝ) : chr (x + y) = chr x * chr y := by
  unfold chr
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem chr_int (n : ℤ) : chr n = 1 := by
  unfold chr
  rw [← Complex.exp_int_mul_two_pi_mul_I n]
  congr 1
  push_cast
  ring

theorem chr_add_int (x : ℝ) (n : ℤ) : chr (x + n) = chr x := by
  rw [chr_add, chr_int, mul_one]

theorem chr_zero : chr 0 = 1 := by simpa using chr_int 0

theorem chr_neg (x : ℝ) : chr (-x) = (chr x)⁻¹ := by
  unfold chr
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem norm_chr (x : ℝ) : ‖chr x‖ = 1 := by
  unfold chr
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.I_re, Complex.I_im]

/-- The character of `ZMod n` sending `m` to `exp (2πi m / n)`. -/
noncomputable def chrZ (n : ℕ) [NeZero n] (m : ZMod n) : ℂ := chr (m.val / n)

theorem chrZ_intCast (n : ℕ) [NeZero n] (r : ℤ) : chrZ n (r : ZMod n) = chr (r / n) := by
  unfold chrZ
  have h : ((r : ZMod n).val : ℝ) = r - n * (r / n : ℤ) := by
    have := ZMod.val_intCast r (n := n)
    have h2 : ((r : ZMod n).val : ℤ) = r - n * (r / n) := by
      rw [this]; exact Int.emod_def r n
    exact_mod_cast h2
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [h, show ((r : ℝ) - n * (r / n : ℤ)) / n = r / n + (-(r / n : ℤ) : ℤ) by
    push_cast
    field_simp
    ring]
  exact chr_add_int _ _

theorem chrZ_natCast (n : ℕ) [NeZero n] (r : ℕ) : chrZ n (r : ZMod n) = chr (r / n) := by
  have := chrZ_intCast n r
  push_cast at this
  exact this

theorem chrZ_add (n : ℕ) [NeZero n] (a b : ZMod n) : chrZ n (a + b) = chrZ n a * chrZ n b := by
  rw [← ZMod.intCast_zmod_cast a, ← ZMod.intCast_zmod_cast b, ← Int.cast_add]
  rw [chrZ_intCast, chrZ_intCast, chrZ_intCast, ← chr_add]
  congr 1
  push_cast
  ring

theorem chrZ_eq_pow (n : ℕ) [NeZero n] (m : ZMod n) :
    chrZ n m = Complex.exp (2 * π * I / n) ^ m.val := by
  unfold chrZ chr
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Orthogonality of the characters of `ZMod n`. -/
theorem sum_chrZ (n : ℕ) [NeZero n] (m : ZMod n) :
    ∑ j : ZMod n, chrZ n (j * m) = if m = 0 then (n : ℂ) else 0 := by
  simp_rw [chrZ_eq_pow]
  exact sum_pow_val (Complex.isPrimitiveRoot_exp n (NeZero.ne n)) m

/-- The paper's normalised transform `(F_n u)_j = n⁻¹ ∑_k e^{-2πi jk/n} u_k`. -/
noncomputable def dftC (n : ℕ) [NeZero n] (u : ZMod n → ℂ) : ZMod n → ℂ :=
  fun j => (1 / n : ℂ) * ∑ k, chrZ n (-(j * k)) * u k

/-- `(S u)_k = α⁻¹ ∑_{j ∈ ℤ} exp (-π α⁻² s² (k/t - j/s)²) u_j`. -/
noncomputable def resampS (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ) (u : ZMod s → ℂ) :
    ZMod t → ℂ :=
  fun k => (1 / α : ℂ) * ∑' j : ℤ,
    (Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℂ) * u j

/-- `(T u)_k = ∑_{j ∈ ℤ} exp (-π α² t² (k/t - j/s)²) u_j`. -/
noncomputable def resampT (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ) (u : ZMod s → ℂ) :
    ZMod t → ℂ :=
  fun k => ∑' j : ℤ,
    (Real.exp (-π * α ^ 2 * t ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℂ) * u j

/-- `(P_s u)_j = u_{tj}`. -/
def permS {s : ℕ} (t : ℕ) (u : ZMod s → ℂ) : ZMod s → ℂ := fun j => u (t * j)

/-- `(P_t u)_k = u_{-sk}`. -/
def permT {t : ℕ} (s : ℕ) (u : ZMod t → ℂ) : ZMod t → ℂ := fun k => u (-(s * k))

/-! ### Shifted Poisson summation for the Gaussian -/

/-- `∑_{n ∈ ℤ} exp (-π a (x + n)²) = a^{-1/2} ∑_{r ∈ ℤ} exp (-π r² / a) e^{2πi r x}`. -/
theorem gauss_poisson_shift {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ∑' n : ℤ, (Real.exp (-π * a * (x + n) ^ 2) : ℂ) =
      (1 / Real.sqrt a : ℂ) * ∑' r : ℤ, (Real.exp (-π * r ^ 2 / a) : ℂ) * chr (r * x) := by
  -- Express the left side through `jacobiTheta₂ (I a x) (I a)`.
  have hL : ∑' n : ℤ, (Real.exp (-π * a * (x + n) ^ 2) : ℂ) =
      Complex.exp (-π * a * x ^ 2) * jacobiTheta₂ (I * a * x) (I * a) := by
    unfold jacobiTheta₂
    rw [← tsum_mul_left]
    congr 1
    funext n
    unfold jacobiTheta₂_term
    rw [← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination (-(2 * π * a * n * x) - π * a * n ^ 2) * Complex.I_sq
  -- Express the right side through `jacobiTheta₂ x (I / a)`.
  have hR : ∑' r : ℤ, (Real.exp (-π * r ^ 2 / a) : ℂ) * chr (r * x) =
      jacobiTheta₂ x (I / a) := by
    unfold jacobiTheta₂
    congr 1
    funext r
    unfold jacobiTheta₂_term chr
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-(π * r ^ 2 / a)) * Complex.I_sq
  rw [hL, hR, jacobiTheta₂_functional_equation (I * a * x) (I * a)]
  have hIa : -I * (I * a) = (a : ℂ) := by linear_combination (-(a : ℂ)) * Complex.I_sq
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hsqrt : ((a : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt a : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le]
    push_cast
    rfl
  have hz : (I * a * x) / (I * a) = (x : ℂ) := by
    field_simp
  have hτ : -1 / (I * a) = I / a := by
    field_simp
    linear_combination (-(1 : ℂ)) * Complex.I_sq
  rw [hIa, hsqrt, hz, hτ]
  have hI2 : (I * a * x) ^ 2 = -((a : ℂ) ^ 2 * x ^ 2) := by
    linear_combination ((a : ℂ) ^ 2 * x ^ 2) * Complex.I_sq
  have hexp : Complex.exp (-π * I * (I * a * x) ^ 2 / (I * a)) = Complex.exp (π * a * x ^ 2) := by
    congr 1
    rw [hI2]
    field_simp
  rw [hexp]
  calc Complex.exp (-π * a * x ^ 2) *
        (1 / (Real.sqrt a : ℂ) * Complex.exp (π * a * x ^ 2) * jacobiTheta₂ x (I / a))
      = (Complex.exp (-π * a * x ^ 2) * Complex.exp (π * a * x ^ 2)) *
          (1 / (Real.sqrt a : ℂ) * jacobiTheta₂ x (I / a)) := by ring
    _ = _ := by
      rw [← Complex.exp_add, show -(π : ℂ) * a * x ^ 2 + π * a * x ^ 2 = 0 by ring,
        Complex.exp_zero, one_mul]

/-! ### Regrouping sums over `ℤ` -/

/-- `ℤ ≃ ZMod s × ℤ` by residue and quotient. -/
def residueEquiv (s : ℕ) [NeZero s] : ZMod s × ℤ ≃ ℤ where
  toFun p := p.2 * s + (p.1.val : ℤ)
  invFun j := ((j : ZMod s), j / s)
  left_inv := by
    rintro ⟨m, q⟩
    have hs : (s : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne s
    simp only [Prod.mk.injEq]
    constructor
    · push_cast
      simp
    · rw [add_comm, Int.add_mul_ediv_right _ _ hs,
        Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast m.val_lt), zero_add]
  right_inv := by
    intro j
    simp only
    rw [ZMod.val_intCast, Int.ediv_mul_add_emod]

theorem residueEquiv_apply (s : ℕ) [NeZero s] (p : ZMod s × ℤ) :
    residueEquiv s p = p.2 * s + (p.1.val : ℤ) := rfl

theorem tsum_regroup (s : ℕ) [NeZero s] (f : ℤ → ℂ) (hf : Summable f) :
    ∑' j : ℤ, f j = ∑ m : ZMod s, ∑' q : ℤ, f (q * s + m.val) := by
  rw [← (residueEquiv s).tsum_eq f]
  have hs : Summable (f ∘ residueEquiv s) := (residueEquiv s).summable_iff.mpr hf
  change ∑' p : ZMod s × ℤ, (f ∘ residueEquiv s) p = _
  rw [Summable.tsum_prod' hs (fun m => hs.prod_factor m), tsum_fintype]
  rfl

theorem tsum_residue_class (t : ℕ) [NeZero t] (F : ℤ → ℂ) (c : ℤ) :
    ∑' r : ℤ, (if (t : ℤ) ∣ r + c then F r else 0) = ∑' j : ℤ, F (t * j - c) := by
  have ht : (t : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have hinj : Function.Injective (fun j : ℤ => (t : ℤ) * j - c) := by
    intro a b h
    simp only at h
    exact mul_left_cancel₀ ht (by linarith)
  have hsupp : Function.support (fun r : ℤ => if (t : ℤ) ∣ r + c then F r else 0) ⊆
      Set.range (fun j : ℤ => (t : ℤ) * j - c) := by
    intro r hr
    rw [Function.mem_support] at hr
    by_cases hd : (t : ℤ) ∣ r + c
    · obtain ⟨j, hj⟩ := hd
      exact ⟨j, by linarith⟩
    · exact absurd (by simp [hd]) hr
  rw [← hinj.tsum_eq hsupp]
  apply tsum_congr
  intro j
  have hd : (t : ℤ) ∣ t * j - c + c := ⟨j, by ring⟩
  simp

/-- Orthogonality in the form used below. -/
theorem sum_chr_div (t : ℕ) [NeZero t] (c : ℤ) :
    ∑ ℓ : ZMod t, chr (c * ℓ.val / t) = if (t : ℤ) ∣ c then (t : ℂ) else 0 := by
  have h : ∀ ℓ : ZMod t, chr (c * ℓ.val / t) = chrZ t (ℓ * c) := by
    intro ℓ
    have := chrZ_intCast t (c * ℓ.val)
    push_cast at this
    rw [ZMod.natCast_zmod_val] at this
    rw [mul_comm ℓ, this]
  simp_rw [h]
  rw [sum_chrZ]
  by_cases hd : (t : ℤ) ∣ c <;> simp [hd, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-! ### Norm and summability facts -/

theorem norm_dftC_le (n : ℕ) [NeZero n] (u : ZMod n → ℂ) (j : ZMod n) :
    ‖dftC n u j‖ ≤ ∑ k, ‖u k‖ := by
  unfold dftC
  rw [norm_mul]
  have h1 : ‖(1 / n : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, Complex.norm_natCast]
    exact div_le_one_of_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
      (by positivity)
  calc ‖(1 / n : ℂ)‖ * ‖∑ k, chrZ n (-(j * k)) * u k‖
      ≤ 1 * ∑ k, ‖chrZ n (-(j * k)) * u k‖ := by
        gcongr
        exact norm_sum_le _ _
    _ = ∑ k, ‖u k‖ := by
        simp [chrZ, norm_chr]

theorem norm_le_sum_norm {n : ℕ} [NeZero n] (u : ZMod n → ℂ) (j : ZMod n) :
    ‖u j‖ ≤ ∑ k, ‖u k‖ :=
  Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

/-- The resampling weight `exp (-π α² r² / s²)` times a bounded sequence is summable. -/
theorem summable_weight_mul {s : ℕ} [NeZero s] {α : ℝ} (hα : 0 < α) (g : ℤ → ℂ) (M : ℝ)
    (hg : ∀ r, ‖g r‖ ≤ M) :
    Summable (fun r : ℤ => (Real.exp (-π * α ^ 2 * r ^ 2 / s ^ 2) : ℂ) * g r) := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hc : 0 < π * α ^ 2 / s ^ 2 := by positivity
  refine Summable.of_norm_bounded (g := fun r : ℤ => gauss (π * α ^ 2 / s ^ 2) (0 + r) * M)
    ((summable_gauss_int hc 0).mul_right M) (fun r => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have : Real.exp (-π * α ^ 2 * r ^ 2 / s ^ 2) = gauss (π * α ^ 2 / s ^ 2) (0 + r) := by
    unfold gauss
    congr 1
    field_simp
    ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (hg r) (gauss_pos _ _).le

/-- The series defining `resampS` converges absolutely. -/
theorem summable_resampS_term {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ} (hα : 0 < α)
    (u : ZMod s → ℂ) (ℓ : ZMod t) :
    Summable (fun j : ℤ =>
      (Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((ℓ.val : ℝ) / t - j / s) ^ 2) : ℂ) * u j) := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hc : 0 < π * α⁻¹ ^ 2 := by positivity
  refine Summable.of_norm_bounded
    (g := fun j : ℤ => gauss (π * α⁻¹ ^ 2) (-(s * ℓ.val / t) + j) * ∑ k, ‖u k‖)
    ((summable_gauss_int hc _).mul_right _) (fun j => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have : Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((ℓ.val : ℝ) / t - j / s) ^ 2) =
      gauss (π * α⁻¹ ^ 2) (-(s * ℓ.val / t) + j) := by
    unfold gauss
    congr 1
    field_simp
    ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (norm_le_sum_norm u _) (gauss_pos _ _).le

/-! ### The resampling identity -/

/-- Poisson summation applied to one residue class of the `S` sum. -/
theorem inner_poisson {s : ℕ} [NeZero s] {α : ℝ} (hα : 0 < α) (x : ℝ) :
    ∑' q : ℤ, (Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * (x - q) ^ 2) : ℂ) =
      (α / s : ℂ) * ∑' r : ℤ, (Real.exp (-π * α ^ 2 * r ^ 2 / s ^ 2) : ℂ) * chr (r * x) := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have ha : 0 < α⁻¹ ^ 2 * s ^ 2 := by positivity
  rw [← (Equiv.neg ℤ).tsum_eq]
  have h1 : ∀ q : ℤ, (Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * (x - ((Equiv.neg ℤ) q : ℤ)) ^ 2) : ℂ) =
      (Real.exp (-π * (α⁻¹ ^ 2 * s ^ 2) * (x + q) ^ 2) : ℂ) := by
    intro q
    simp only [Equiv.neg_apply, Int.cast_neg, sub_neg_eq_add]
    ring_nf
  simp_rw [h1]
  rw [gauss_poisson_shift ha x]
  congr 1
  · rw [show α⁻¹ ^ 2 * s ^ 2 = (s / α) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    push_cast
    field_simp
  · apply tsum_congr
    intro r
    congr 2
    field_simp

/-- `(S u)_ℓ = ∑_{r ∈ ℤ} exp (-π α² r² / s²) e^{2πi r ℓ / t} (F_s u)_r`. -/
theorem resampS_eq {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ} (hα : 0 < α)
    (u : ZMod s → ℂ) (ℓ : ZMod t) :
    resampS s t α u ℓ = ∑' r : ℤ,
      (Real.exp (-π * α ^ 2 * r ^ 2 / s ^ 2) : ℂ) * (chr (r * ℓ.val / t) * dftC s u r) := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne s
  have hαC : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  unfold resampS
  rw [tsum_regroup s _ (summable_resampS_term hα u ℓ)]
  -- Evaluate each residue class.
  have hclass : ∀ m : ZMod s,
      ∑' q : ℤ, (Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 *
          ((ℓ.val : ℝ) / t - ((q * s + m.val : ℤ) : ℝ) / s) ^ 2) : ℂ) * u ((q * s + m.val : ℤ)) =
      (α / s : ℂ) * ∑' r : ℤ, (Real.exp (-π * α ^ 2 * r ^ 2 / s ^ 2) : ℂ) *
        (chr (r * ℓ.val / t) * (chr (-(r * m.val / s)) * u m)) := by
    intro m
    have hu : ∀ q : ℤ, u ((q * s + m.val : ℤ)) = u m := by
      intro q
      congr 1
      push_cast
      simp
    have hx : ∀ q : ℤ, ((ℓ.val : ℝ) / t - ((q * s + m.val : ℤ) : ℝ) / s) =
        ((ℓ.val : ℝ) / t - m.val / s) - q := by
      intro q
      push_cast
      field_simp
      ring
    simp_rw [hu, hx]
    rw [tsum_mul_right, inner_poisson hα, mul_assoc, ← tsum_mul_right]
    congr 1
    apply tsum_congr
    intro r
    rw [show (r : ℝ) * ((ℓ.val : ℝ) / t - m.val / s) = r * ℓ.val / t + (-(r * m.val / s)) by ring,
      chr_add]
    ring
  simp_rw [hclass]
  -- Swap the finite sum with the series.
  have hsum : ∀ m : ZMod s, Summable (fun r : ℤ => (Real.exp (-π * α ^ 2 * r ^ 2 / s ^ 2) : ℂ) *
      (chr (r * ℓ.val / t) * (chr (-(r * m.val / s)) * u m))) := by
    intro m
    refine summable_weight_mul hα _ (‖u m‖) (fun r => ?_)
    rw [norm_mul, norm_mul, norm_chr, norm_chr, one_mul, one_mul]
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (fun m _ => hsum m), ← tsum_mul_left,
    ← tsum_mul_left]
  apply tsum_congr
  intro r
  unfold dftC
  have hchr : ∀ k : ZMod s, chrZ s (-((r : ZMod s) * k)) = chr (-(r * k.val / s)) := by
    intro k
    have := chrZ_intCast s (-(r * k.val))
    push_cast at this
    rw [ZMod.natCast_zmod_val] at this
    rw [this, neg_div]
  simp_rw [hchr]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

/-- Theorem 4.2 of Harvey and van der Hoeven: `T ∘ P_s ∘ F_s = P_t ∘ F_t ∘ S`. -/
theorem resampling_identity {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ} (hα : 0 < α)
    (u : ZMod s → ℂ) :
    resampT s t α (permS t (dftC s u)) = permT s (dftC t (resampS s t α u)) := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have ht : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t)
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  funext k
  unfold permT
  conv_rhs => unfold dftC
  simp_rw [resampS_eq hα u]
  have hchr : ∀ ℓ : ZMod t, chrZ t (-(-((s : ZMod t) * k) * ℓ)) =
      chr (((s * k.val : ℤ) : ℝ) * ℓ.val / t) := by
    intro ℓ
    push_cast
    have := chrZ_intCast t ((s * k.val : ℤ) * ℓ.val)
    push_cast at this
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
    rw [← this]
    congr 1
    ring
  simp_rw [hchr]
  have hsum : ∀ ℓ : ZMod t, Summable (fun r : ℤ => chr (((s * k.val : ℤ) : ℝ) * ℓ.val / t) *
      ((Real.exp (-π * α ^ 2 * r ^ 2 / s ^ 2) : ℂ) * (chr (r * ℓ.val / t) * dftC s u r))) := by
    intro ℓ
    refine (summable_weight_mul hα _ (∑ j, ‖u j‖) (fun r => ?_)).mul_left _
    rw [norm_mul, norm_chr, one_mul]
    exact norm_dftC_le s u r
  have h2 : ∀ ℓ : ZMod t, chr (((s * k.val : ℤ) : ℝ) * ℓ.val / t) *
      ∑' r : ℤ, (Real.exp (-π * α ^ 2 * r ^ 2 / s ^ 2) : ℂ) * (chr (r * ℓ.val / t) * dftC s u r) =
      ∑' r : ℤ, chr (((s * k.val : ℤ) : ℝ) * ℓ.val / t) *
        ((Real.exp (-π * α ^ 2 * r ^ 2 / s ^ 2) : ℂ) * (chr (r * ℓ.val / t) * dftC s u r)) :=
    fun ℓ => (tsum_mul_left).symm
  simp_rw [h2]
  rw [← Summable.tsum_finsetSum (fun ℓ _ => hsum ℓ), ← tsum_mul_left]
  have hinner : ∀ r : ℤ, (1 / t : ℂ) * ∑ ℓ : ZMod t, chr (((s * k.val : ℤ) : ℝ) * ℓ.val / t) *
      ((Real.exp (-π * α ^ 2 * r ^ 2 / s ^ 2) : ℂ) * (chr (r * ℓ.val / t) * dftC s u r)) =
      if (t : ℤ) ∣ r + s * k.val then
        (Real.exp (-π * α ^ 2 * r ^ 2 / s ^ 2) : ℂ) * dftC s u r else 0 := by
    intro r
    have h1 : ∀ ℓ : ZMod t, chr (((s * k.val : ℤ) : ℝ) * ℓ.val / t) *
        ((Real.exp (-π * α ^ 2 * r ^ 2 / s ^ 2) : ℂ) * (chr (r * ℓ.val / t) * dftC s u r)) =
        chr (((r + s * k.val : ℤ) : ℝ) * ℓ.val / t) *
          ((Real.exp (-π * α ^ 2 * r ^ 2 / s ^ 2) : ℂ) * dftC s u r) := by
      intro ℓ
      push_cast
      rw [show ((r : ℝ) + s * k.val) * ℓ.val / t = r * ℓ.val / t + (s * k.val) * ℓ.val / t by ring,
        chr_add]
      ring
    simp_rw [h1]
    rw [← Finset.sum_mul, sum_chr_div]
    split_ifs
    · field_simp
    · simp
  simp_rw [hinner]
  rw [tsum_residue_class]
  unfold resampT permS
  apply tsum_congr
  intro j
  congr 1
  · congr 1
    push_cast
    field_simp
    ring_nf
  · congr 1
    push_cast
    simp

end IntegerMultBounds.NLogN
