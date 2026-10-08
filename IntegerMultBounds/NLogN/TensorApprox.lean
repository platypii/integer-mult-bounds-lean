import IntegerMultBounds.NLogN.Approx
import IntegerMultBounds.NLogN.Multidim

/-! The two-factor case of Lemma 2.11 of Harvey and van der Hoeven. Proved:
slice-wise application along the second coordinate keeps the error and norm
bounds (mirroring the first-coordinate case in `Approx.lean`); applying one
approximation on every first-coordinate slice and another on every
second-coordinate slice approximates the tensor product with the sum of the
two errors; and the two-dimensional transform, normalized or not, is exactly
such a tensor product of one-dimensional transforms. The `d`-fold version
follows by induction on the coordinates and is not written here. -/

open Complex

namespace IntegerMultBounds.NLogN

section Slice₂

variable {n n' : ℕ} {α : Type*} [Fintype α]

/-- Apply a map on `Fin n → ℂ` to every `α`-slice of `α × Fin n → ℂ` (second factor). -/
def sliceMap₂ (A : (Fin n → ℂ) → (Fin n' → ℂ)) : (α × Fin n → ℂ) → (α × Fin n' → ℂ) :=
  fun u aj => A (fun i => u (aj.1, i)) aj.2

/-- Restriction to one second-factor slice, as a continuous linear map. -/
noncomputable def restrictSlice₂ (a : α) : (α × Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (a, i)

/-- The second-factor slice-wise action of a continuous linear map. -/
noncomputable def sliceCLM₂ (A : (Fin n → ℂ) →L[ℂ] (Fin n' → ℂ)) :
    (α × Fin n → ℂ) →L[ℂ] (α × Fin n' → ℂ) :=
  ContinuousLinearMap.pi fun aj =>
    (ContinuousLinearMap.proj aj.2).comp (A.comp (restrictSlice₂ aj.1))

omit [Fintype α] in
theorem sliceCLM₂_apply (A : (Fin n → ℂ) →L[ℂ] (Fin n' → ℂ)) (u : α × Fin n → ℂ) :
    sliceCLM₂ A u = sliceMap₂ A u := by
  funext aj
  simp [sliceCLM₂, restrictSlice₂, sliceMap₂]

theorem norm_slice₂_le (u : α × Fin n → ℂ) (a : α) : ‖fun i => u (a, i)‖ ≤ ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  exact norm_le_pi_norm u (a, i)

theorem norm_sliceMap₂_le (A : (Fin n → ℂ) → (Fin n' → ℂ)) (u : α × Fin n → ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hA : ∀ a : α, ‖A (fun i => u (a, i))‖ ≤ M) :
    ‖sliceMap₂ A u‖ ≤ M := by
  rw [pi_norm_le_iff_of_nonneg hM]
  intro aj
  calc ‖sliceMap₂ A u aj‖ = ‖A (fun i => u (aj.1, i)) aj.2‖ := rfl
    _ ≤ ‖A (fun i => u (aj.1, i))‖ := norm_le_pi_norm _ _
    _ ≤ M := hA aj.1

theorem opNorm_sliceCLM₂_le (A : (Fin n → ℂ) →L[ℂ] (Fin n' → ℂ)) (hA : ‖A‖ ≤ 1) :
    ‖sliceCLM₂ (α := α) A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [sliceCLM₂_apply, one_mul]
  apply norm_sliceMap₂_le _ _ (norm_nonneg _)
  intro a
  calc ‖A (fun i => u (a, i))‖ ≤ ‖A‖ * ‖fun i => u (a, i)‖ := A.le_opNorm _
    _ ≤ 1 * ‖u‖ := by gcongr; exact norm_slice₂_le u a
    _ = ‖u‖ := one_mul _

/-- Lemma 2.11 along the second coordinate: slice-wise application keeps the error. -/
theorem approxMap_sliceMap₂ {p : ℕ} {A' : (Fin n → ℂ) → (Fin n' → ℂ)}
    {A : (Fin n → ℂ) →L[ℂ] (Fin n' → ℂ)} {ε : ℝ} (hA' : ApproxMap p A' A ε) :
    ApproxMap p (sliceMap₂ (α := α) A') (sliceCLM₂ A) ε := by
  intro u hu
  have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
  have hε : 0 ≤ ε := by
    have := hA' 0 (by simp)
    exact le_trans (by positivity) this
  rw [sliceCLM₂_apply]
  have : ‖sliceMap₂ A' u - sliceMap₂ A u‖ ≤ ε / 2 ^ p := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro aj
    have h := hA' (fun i => u (aj.1, i)) (le_trans (norm_slice₂_le u aj.1) hu)
    calc ‖(sliceMap₂ A' u - sliceMap₂ A u) aj‖
        = ‖(A' (fun i => u (aj.1, i)) - A (fun i => u (aj.1, i))) aj.2‖ := rfl
      _ ≤ ‖A' (fun i => u (aj.1, i)) - A (fun i => u (aj.1, i))‖ := norm_le_pi_norm _ _
      _ ≤ ε / 2 ^ p := by
          rw [le_div_iff₀ (by positivity)]
          linarith
  calc 2 ^ p * ‖sliceMap₂ A' u - sliceMap₂ A u‖ ≤ 2 ^ p * (ε / 2 ^ p) := by gcongr
    _ = ε := by field_simp

theorem sliceMap₂_ball {A' : (Fin n → ℂ) → (Fin n' → ℂ)}
    (hA'ball : ∀ v, ‖v‖ ≤ 1 → ‖A' v‖ ≤ 1) (u : α × Fin n → ℂ) (hu : ‖u‖ ≤ 1) :
    ‖sliceMap₂ (α := α) A' u‖ ≤ 1 :=
  norm_sliceMap₂_le _ _ zero_le_one fun a => hA'ball _ (le_trans (norm_slice₂_le u a) hu)

end Slice₂

section Tensor

variable {m m' n n' : ℕ}

/-- Apply `A₁'` on every first-coordinate slice, then `A₂'` on every second-coordinate
slice: the computable shape of a tensor product of approximations. -/
def tensorApprox (A₁' : (Fin m → ℂ) → (Fin m' → ℂ)) (A₂' : (Fin n → ℂ) → (Fin n' → ℂ)) :
    (Fin m × Fin n → ℂ) → (Fin m' × Fin n' → ℂ) :=
  sliceMap₂ A₂' ∘ sliceMap A₁'

/-- The exact tensor product of two continuous linear maps, as slice actions. -/
noncomputable def tensorCLM (A₁ : (Fin m → ℂ) →L[ℂ] (Fin m' → ℂ))
    (A₂ : (Fin n → ℂ) →L[ℂ] (Fin n' → ℂ)) :
    (Fin m × Fin n → ℂ) →L[ℂ] (Fin m' × Fin n' → ℂ) :=
  sliceCLM₂ A₂ ∘L sliceCLM A₁

theorem tensorCLM_apply (A₁ : (Fin m → ℂ) →L[ℂ] (Fin m' → ℂ))
    (A₂ : (Fin n → ℂ) →L[ℂ] (Fin n' → ℂ)) (u : Fin m × Fin n → ℂ) :
    tensorCLM A₁ A₂ u = sliceMap₂ A₂ (sliceMap A₁ u) := by
  simp only [tensorCLM, ContinuousLinearMap.comp_apply, sliceCLM₂_apply, sliceCLM_apply]

theorem opNorm_tensorCLM_le (A₁ : (Fin m → ℂ) →L[ℂ] (Fin m' → ℂ))
    (A₂ : (Fin n → ℂ) →L[ℂ] (Fin n' → ℂ)) (h₁ : ‖A₁‖ ≤ 1) (h₂ : ‖A₂‖ ≤ 1) :
    ‖tensorCLM A₁ A₂‖ ≤ 1 := by
  calc ‖tensorCLM A₁ A₂‖ ≤ ‖sliceCLM₂ (α := Fin m') A₂‖ * ‖sliceCLM (β := Fin n) A₁‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := by gcongr; exacts [opNorm_sliceCLM₂_le _ h₂, opNorm_sliceCLM_le _ h₁]
    _ = 1 := one_mul _

/-- Lemma 2.11 with two factors: the tensor approximation's error is the sum of the errors. -/
theorem approxMap_tensor {p : ℕ} {A₁' : (Fin m → ℂ) → (Fin m' → ℂ)}
    {A₁ : (Fin m → ℂ) →L[ℂ] (Fin m' → ℂ)} {A₂' : (Fin n → ℂ) → (Fin n' → ℂ)}
    {A₂ : (Fin n → ℂ) →L[ℂ] (Fin n' → ℂ)} {ε₁ ε₂ : ℝ} (hA₂ : ‖A₂‖ ≤ 1)
    (h₁ : ApproxMap p A₁' A₁ ε₁) (h₂ : ApproxMap p A₂' A₂ ε₂)
    (h₁ball : ∀ u, ‖u‖ ≤ 1 → ‖A₁' u‖ ≤ 1) :
    ApproxMap p (tensorApprox A₁' A₂') (tensorCLM A₁ A₂) (ε₂ + ε₁) :=
  approx_comp (opNorm_sliceCLM₂_le _ hA₂) (approxMap_sliceMap h₁) (approxMap_sliceMap₂ h₂)
    (fun u hu => sliceMap_ball h₁ball u hu)

theorem tensorApprox_ball {A₁' : (Fin m → ℂ) → (Fin m' → ℂ)}
    {A₂' : (Fin n → ℂ) → (Fin n' → ℂ)} (h₁ : ∀ u, ‖u‖ ≤ 1 → ‖A₁' u‖ ≤ 1)
    (h₂ : ∀ u, ‖u‖ ≤ 1 → ‖A₂' u‖ ≤ 1) (u : Fin m × Fin n → ℂ) (hu : ‖u‖ ≤ 1) :
    ‖tensorApprox A₁' A₂' u‖ ≤ 1 :=
  sliceMap₂_ball h₂ _ (sliceMap_ball h₁ u hu)

end Tensor

section DFT2

variable {m₀ n₀ : ℕ}

/-- The two-dimensional transform is the second-coordinate transform on every slice
followed by the first-coordinate transform on every slice. -/
theorem dft2_eq_tensor (ζ₁ ζ₂ : ℂ) (a : ZMod (m₀ + 1) × ZMod (n₀ + 1) → ℂ) :
    dft2 ζ₁ ζ₂ a =
      sliceMap (β := Fin (n₀ + 1)) (dft (N := m₀ + 1) ζ₁)
        (sliceMap₂ (α := Fin (m₀ + 1)) (dft (N := n₀ + 1) ζ₂) a) := by
  rw [dft2_eq_rows_cols]
  rfl

/-- The normalized one-dimensional transform `(1/N) ∑ ζ^{jk} a_j`. -/
noncomputable def dftNormZ (N : ℕ) [NeZero N] (ζ : ℂ) (a : ZMod N → ℂ) : ZMod N → ℂ :=
  fun k => (1 / (N : ℂ)) * dft ζ a k

/-- The normalized two-dimensional transform is the tensor of the normalized
one-dimensional ones. -/
theorem dft2_norm_eq_tensor (ζ₁ ζ₂ : ℂ) (a : ZMod (m₀ + 1) × ZMod (n₀ + 1) → ℂ) :
    (fun k => (1 / ((m₀ + 1 : ℕ) * (n₀ + 1 : ℕ) : ℂ)) * dft2 ζ₁ ζ₂ a k) =
      sliceMap (β := Fin (n₀ + 1)) (dftNormZ (m₀ + 1) ζ₁)
        (sliceMap₂ (α := Fin (m₀ + 1)) (dftNormZ (n₀ + 1) ζ₂) a) := by
  funext k
  rw [dft2_eq_rows_cols]
  show _ = (1 / ((m₀ + 1 : ℕ) : ℂ)) *
    dft ζ₁ (fun i => (1 / ((n₀ + 1 : ℕ) : ℂ)) * dft ζ₂ (fun j => a (i, j)) k.2) k.1
  have h : (fun i : ZMod (m₀ + 1) => (1 / ((n₀ + 1 : ℕ) : ℂ)) * dft ζ₂ (fun j => a (i, j)) k.2)
      = (1 / ((n₀ + 1 : ℕ) : ℂ)) • (fun i : ZMod (m₀ + 1) => dft ζ₂ (fun j => a (i, j)) k.2) := by
    funext i; simp [smul_eq_mul]
  rw [h, dft_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  field_simp

end DFT2

end IntegerMultBounds.NLogN
