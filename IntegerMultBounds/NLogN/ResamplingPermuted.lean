import IntegerMultBounds.NLogN.ResamplingAssembly
import IntegerMultBounds.NLogN.Bluestein

/-! Resampling with the permutations left in the transform (§7). The one
dimensional factorization `F_s = 2^γ B F_t A` of `ResamplingAssembly` carries
`B = P_s⁻¹ D J C P_t`; moving `P_s` to the left gives
`P_s F_s = 2^γ B₀ P_t F_t A` with `B₀ = D J C / 2^(γ-1)`, a contraction, so
neither coordinate permutation has to be executed. The retained frequency
permutation `Q : j ↦ (-sᵢ jᵢ)ᵢ` of the power-of-two transform is a chirp
identity with the weighted chirp `exp(π i Σ sᵢ jᵢ² / tᵢ)`, and the retained
source permutation `R : j ↦ (cᵢ jᵢ)ᵢ` by units commutes with the transform up
to inversion, `F R = R⁻¹ F`, so it cancels in a convolution. Costs are not
part of this file. -/

namespace IntegerMultBounds.NLogN

open ContinuousLinearMap Complex Real

/-! ### The one-dimensional factorization with `P_s` on the left -/

section OneDimensional

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- The paper's `B₀ = D' J' C = D J C / 2^(γ-1)`: no permutation. -/
noncomputable def resampB₀ (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 1))⁻¹ • (diagDCLM s t α ∘L J ∘L rowSelectCLM s t)

theorem resampB_eq (hcop : Nat.Coprime s t) (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) :
    resampB s t α hcop J =
      ((permSEquiv hcop).symm : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) ∘L
        (resampB₀ s t α J ∘L permTCLM s) := by
  unfold resampB resampB₀
  ext u j
  simp only [comp_apply, smul_apply, map_smul]

/-- `‖B₀‖ ≤ 1` for a left inverse `J` with `‖J‖ ≤ 2`. -/
theorem opNorm_resampB₀_le (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : ‖J‖ ≤ 2) :
    ‖resampB₀ s t α J‖ ≤ 1 := by
  unfold resampB₀
  have hD := opNorm_diagDCLM_le_pow s t α
  have hC := opNorm_rowSelectCLM_le s t
  have hJ0 : 0 ≤ ‖J‖ := norm_nonneg _
  have hcomp : ‖diagDCLM s t α ∘L J ∘L rowSelectCLM s t‖ ≤ (2 : ℝ) ^ (2 * ⌈α ^ 2⌉₊) * 2 := by
    calc ‖diagDCLM s t α ∘L J ∘L rowSelectCLM s t‖
        ≤ ‖diagDCLM s t α‖ * ‖J ∘L rowSelectCLM s t‖ := opNorm_comp_le _ _
      _ ≤ ‖diagDCLM s t α‖ * (‖J‖ * ‖rowSelectCLM s t‖) := by
          gcongr
          exact opNorm_comp_le _ _
      _ ≤ (2 : ℝ) ^ (2 * ⌈α ^ 2⌉₊) * (2 * 1) := by gcongr
      _ = (2 : ℝ) ^ (2 * ⌈α ^ 2⌉₊) * 2 := by ring
  have hnorm : ‖((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 1))⁻¹‖ = ((2 : ℝ) ^ (2 * ⌈α ^ 2⌉₊ + 1))⁻¹ := by
    rw [norm_inv, norm_pow]
    norm_num
  calc ‖((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 1))⁻¹ • (diagDCLM s t α ∘L J ∘L rowSelectCLM s t)‖
      ≤ ‖((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 1))⁻¹‖ * ‖diagDCLM s t α ∘L J ∘L rowSelectCLM s t‖ :=
        opNorm_smul_le _ _
    _ ≤ ((2 : ℝ) ^ (2 * ⌈α ^ 2⌉₊ + 1))⁻¹ * ((2 : ℝ) ^ (2 * ⌈α ^ 2⌉₊) * 2) := by
        rw [hnorm]
        gcongr
    _ = 1 := by
        rw [pow_succ]
        field_simp

/-- Lemma 7.1, the exact identity: `P_s F_s = 2^γ B₀ P_t F_t A`, with `‖A‖ ≤ 1` and
`‖B₀‖ ≤ 1`, for `s < t` coprime, `α ≥ 1`, and `α² θ ≥ 1`. -/
theorem permuted_factorization (hst : s < t) (hcop : Nat.Coprime s t) (hα : 1 ≤ α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) :
    ∃ J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ),
      permSCLM t ∘L dftCLM s = ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 2)) •
        (resampB₀ s t α J ∘L permTCLM s ∘L dftCLM t ∘L resampA s t α) ∧
      ‖resampA s t α‖ ≤ 1 ∧ ‖resampB₀ s t α J‖ ≤ 1 := by
  obtain ⟨J, hJ, -, hJn⟩ := exists_left_inverse hst (by linarith) hθ
  obtain ⟨heq, hA, -⟩ := resampling_factorization_explicit hst hcop hα hθ J hJ
  refine ⟨J, ?_, hA, opNorm_resampB₀_le J hJn⟩
  rw [resampB_eq hcop J] at heq
  rw [← permSEquiv_coe hcop, heq]
  ext u j
  simp only [comp_apply, smul_apply, map_smul, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

end OneDimensional

/-! ### The retained frequency permutation as a weighted chirp -/

section Chirp

variable {t : ℕ} [NeZero t]

/-- `exp(2πi x / t)` depends only on `x` modulo `t`. -/
theorem chirpExp_two_congr {x y : ℤ} (h : (x : ZMod t) = y) :
    chirpExp t (2 * x) = chirpExp t (2 * y) := by
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub x y t).mp h
  have : 2 * y = 2 * x + 2 * t * q := by rw [show y = x + t * q by linarith]; ring
  rw [this, chirpExp_add_mul]

/-- The weighted chirp `e^{π i s j² / t}`. -/
noncomputable def chirpS (t s : ℕ) (j : ZMod t) : ℂ := chirpExp t (s * (j.val : ℤ) ^ 2)

theorem chirpS_sub_mul (ht : 2 ∣ t) (s : ℕ) (j k : ZMod t) :
    (starRingEnd ℂ) (chirpS t s (j - k)) * chirpS t s j * chirpS t s k =
      chirpExp t (2 * (s * j.val * k.val)) := by
  obtain ⟨q, hq⟩ := val_sub_eq j k
  obtain ⟨t', ht'⟩ := ht
  have hshift : chirpS t s (j - k) = chirpExp t (s * ((j.val : ℤ) - k.val) ^ 2) := by
    unfold chirpS
    rw [hq]
    have : (s : ℤ) * ((j.val : ℤ) - k.val + t * q) ^ 2 =
        s * ((j.val : ℤ) - k.val) ^ 2 + 2 * t * (s * q * ((j.val : ℤ) - k.val) + s * t' * q ^ 2) := by
      rw [show (t : ℤ) = 2 * t' by exact_mod_cast ht']
      ring
    rw [this, chirpExp_add_mul]
  rw [hshift, chirpExp_conj]
  unfold chirpS
  rw [chirpExp_mul, chirpExp_mul]
  congr 1
  ring

variable {d : ℕ} {N : Fin d → ℕ} [∀ i, NeZero (N i)]

/-- The multidimensional weighted chirp. -/
noncomputable def chirpW (N : Fin d → ℕ) (s : Fin d → ℕ) (j : (i : Fin d) → ZMod (N i)) : ℂ :=
  ∏ i, chirpS (N i) (s i) (j i)

/-- The retained frequency permutation `Q : j ↦ (-sᵢ jᵢ)ᵢ`. -/
def permQ (s : Fin d → ℕ) (j : (i : Fin d) → ZMod (N i)) : (i : Fin d) → ZMod (N i) :=
  fun i => -((s i : ZMod (N i)) * j i)

theorem root_pow_permQ (ht : 2 ∣ t) (s : ℕ) (j k : ZMod t) :
    Complex.exp (-2 * π * I / t) ^ (k * -((s : ZMod t) * j)).val =
      (starRingEnd ℂ) (chirpS t s (j - k)) * chirpS t s j * chirpS t s k := by
  rw [omega_pow_val, chirpS_sub_mul ht, exp_neg_two_eq]
  have hcast : ((-((k.val * (-((s : ZMod t) * j)).val : ℕ) : ℤ) : ℤ) : ZMod t) =
      ((s * j.val * k.val : ℤ) : ZMod t) := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  have h := chirpExp_two_congr (t := t) hcast
  rw [show (-2 : ℤ) * ((k.val * (-((s : ZMod t) * j)).val : ℕ) : ℤ) =
    2 * -((k.val * (-((s : ZMod t) * j)).val : ℕ) : ℤ) by ring]
  exact h

/-- Lemma 7.3, first identity: the permuted power-of-two transform is a pointwise
chirp multiplication, a cyclic convolution with the conjugate chirp, and
another chirp multiplication (no `1/T` factor in this normalization). -/
theorem permuted_bluesteinD (hN : ∀ i, 2 ∣ N i) (s : Fin d → ℕ)
    (u : ((i : Fin d) → ZMod (N i)) → ℂ) :
    (fun j => dftD (fun i => Complex.exp (-2 * π * I / (N i))) u (permQ s j)) =
      fun j => chirpW N s j *
        convG (fun k => chirpW N s k * u k) (fun k => (starRingEnd ℂ) (chirpW N s k)) j := by
  funext j
  simp only [dftD, convG, Finset.mul_sum, chirpW, map_prod, permQ]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : ∀ i, Complex.exp (-2 * π * I / (N i)) ^ (k i * -((s i : ZMod (N i)) * j i)).val =
      (starRingEnd ℂ) (chirpS (N i) (s i) (j i - k i)) * chirpS (N i) (s i) (j i) *
        chirpS (N i) (s i) (k i) := fun i => root_pow_permQ (hN i) (s i) (j i) (k i)
  simp only [Pi.sub_apply, h, Finset.prod_mul_distrib]
  ring

end Chirp

/-! ### The retained source permutation commutes with the transform -/

section Source

variable {R : Type*} [CommRing R]

/-- One dimension: `F (z ∘ (c ·)) = (F z) ∘ (c⁻¹ ·)` for a unit `c`, any root. -/
theorem dft_mulLeft {M : ℕ} [NeZero M] (ζ : R) (c : (ZMod M)ˣ) (z : ZMod M → R) :
    dft ζ (fun k => z ((c : ZMod M) * k)) =
      fun j => dft ζ z (((c⁻¹ : (ZMod M)ˣ) : ZMod M) * j) := by
  funext j
  simp only [dft]
  refine Fintype.sum_equiv (Units.mulLeft c) _ _ fun k => ?_
  simp only [Units.mulLeft_apply]
  congr 2
  rw [mul_mul_mul_comm, Units.mul_inv, one_mul]

variable {d : ℕ} {N : Fin d → ℕ} [∀ i, NeZero (N i)]

/-- The retained source permutation `R : k ↦ (cᵢ kᵢ)ᵢ` by coordinatewise units. -/
def permR (c : (i : Fin d) → (ZMod (N i))ˣ) (z : ((i : Fin d) → ZMod (N i)) → R) :
    ((i : Fin d) → ZMod (N i)) → R :=
  fun k => z fun i => (c i : ZMod (N i)) * k i

omit [CommRing R] [∀ i, NeZero (N i)] in
theorem permR_inv (c : (i : Fin d) → (ZMod (N i))ˣ) (z : ((i : Fin d) → ZMod (N i)) → R) :
    permR c (permR (fun i => (c i)⁻¹) z) = z := by
  funext k
  simp only [permR]
  congr 1
  funext i
  rw [← mul_assoc, Units.inv_mul, one_mul]

omit [∀ i, NeZero (N i)] in
theorem permR_mul (c : (i : Fin d) → (ZMod (N i))ˣ) (u v : ((i : Fin d) → ZMod (N i)) → R) :
    (fun k => permR c u k * permR c v k) = permR c fun k => u k * v k := rfl

/-- `d` dimensions: `F R = R⁻¹ F` for any roots. -/
theorem dftD_permR (ζ : Fin d → R) (c : (i : Fin d) → (ZMod (N i))ˣ)
    (z : ((i : Fin d) → ZMod (N i)) → R) :
    dftD ζ (permR c z) = permR (fun i => (c i)⁻¹) (dftD ζ z) := by
  funext j
  simp only [dftD, permR]
  refine Fintype.sum_equiv (Equiv.piCongrRight fun i => Units.mulLeft (c i)) _ _ fun k => ?_
  simp only [Equiv.piCongrRight_apply, Pi.map_apply, Units.mulLeft_apply]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_mul_mul_comm, Units.mul_inv, one_mul]

/-- Lemma 7.3, second identity, in the unnormalized convention: the retained
source permutation cancels in a convolution,
`R F [(R F u) · (R F v)] = (∏ Nᵢ) (u ∗ v)(-k)`. -/
theorem source_permutation_cancel [IsDomain R] {ζ : Fin d → R}
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) (N i)) (c : (i : Fin d) → (ZMod (N i))ˣ)
    (u v : ((i : Fin d) → ZMod (N i)) → R) :
    permR c (dftD ζ fun k => permR c (dftD ζ u) k * permR c (dftD ζ v) k) =
      fun k => (∏ i, (N i : R)) * convG u v (-k) := by
  rw [permR_mul, show (fun k => dftD ζ u k * dftD ζ v k) = dftD ζ (convG u v) from
    (dftD_convG hζ u v).symm, dftD_permR, permR_inv, dftD_dftD hζ]

end Source

end IntegerMultBounds.NLogN
