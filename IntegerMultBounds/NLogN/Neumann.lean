import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! The linear-algebra skeleton of Harvey–van der Hoeven, Proposition 4.7(i),
separated from the Gaussian analysis. Proved: a Neumann-series inverse of
`1 + E` with `‖E‖ < 1` and its norm bound; the assembly of `F_s = B F_t A`
from the resampling identity `T P_s F_s = P_t F_t S`, the normalisation
`C T D = 1 + E`, and invertibility of `D`, with honest norm bounds; the
scaled normal form `F_s = 2^γ (B' F_t A')` with `‖A'‖, ‖B'‖ ≤ 1`; and the
sup-norm operator bounds for diagonal and coordinate-selection maps. The
resampling identity, the estimate `‖E‖ < 1`, and all costs are not here. -/

namespace IntegerMultBounds.NLogN

open ContinuousLinearMap

section Neumann

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- Neumann series: `1 + E` is invertible when `‖E‖ < 1`, with inverse of norm
at most `1 / (1 - ‖E‖)`. -/
theorem exists_inverse_of_norm_lt_one (E : V →L[ℂ] V) (hE : ‖E‖ < 1) :
    ∃ J : V →L[ℂ] V, J ∘L (1 + E) = 1 ∧ (1 + E) ∘L J = 1 ∧ ‖J‖ ≤ 1 / (1 - ‖E‖) := by
  have h : ‖-E‖ < 1 := by rwa [norm_neg]
  refine ⟨∑' n : ℕ, (-E) ^ n, ?_, ?_, ?_⟩
  · have := geom_series_mul_neg (-E) h
    rwa [sub_neg_eq_add, mul_def] at this
  · have := mul_neg_geom_series (-E) h
    rwa [sub_neg_eq_add, mul_def] at this
  · have h1 : ‖(1 : V →L[ℂ] V)‖ ≤ 1 := by
      rw [one_def]; exact norm_id_le
    calc ‖∑' n : ℕ, (-E) ^ n‖ ≤ ‖(1 : V →L[ℂ] V)‖ - 1 + (1 - ‖-E‖)⁻¹ :=
          tsum_geometric_le_of_norm_lt_one _ h
      _ ≤ 1 / (1 - ‖E‖) := by rw [norm_neg, one_div]; linarith

end Neumann

section Assembly

variable {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] [CompleteSpace U]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- From `T P_s F_s = P_t F_t S`, `C T D = 1 + E` with `‖E‖ < 1`, and `D D' = D' D = 1`,
we get `F_s = B F_t A` with `A = S` and `B = P_s⁻¹ D (1 + E)⁻¹ C P_t`. -/
theorem assemble (Fs : U →L[ℂ] U) (Ft : W →L[ℂ] W) (S T : U →L[ℂ] W) (Ps : U ≃L[ℂ] U)
    (Pt : W →L[ℂ] W) (C : W →L[ℂ] U) (D D' E : U →L[ℂ] U)
    (hres : T ∘L (Ps : U →L[ℂ] U) ∘L Fs = Pt ∘L Ft ∘L S)
    (hN : C ∘L T ∘L D = 1 + E) (hE : ‖E‖ < 1) (hD : D ∘L D' = 1) :
    ∃ A : U →L[ℂ] W, ∃ B : W →L[ℂ] U, Fs = B ∘L Ft ∘L A ∧ ‖A‖ ≤ ‖S‖ ∧
      ‖B‖ ≤ ‖(Ps.symm : U →L[ℂ] U)‖ * ‖D‖ * (1 / (1 - ‖E‖)) * ‖C‖ * ‖Pt‖ := by
  obtain ⟨J, hJ1, -, hJ⟩ := exists_inverse_of_norm_lt_one E hE
  refine ⟨S, (Ps.symm : U →L[ℂ] U) ∘L D ∘L J ∘L C ∘L Pt, ?_, le_rfl, ?_⟩
  · ext x
    have h1 : Pt (Ft (S x)) = T (Ps (Fs x)) := by
      have := congrArg (fun f => f x) hres
      simpa using this.symm
    have h2 : D (D' (Ps (Fs x))) = Ps (Fs x) := by
      have := congrArg (fun f => f (Ps (Fs x))) hD
      simpa using this
    have h3 : C (T (D (D' (Ps (Fs x))))) = (1 + E) (D' (Ps (Fs x))) := by
      have := congrArg (fun f => f (D' (Ps (Fs x)))) hN
      simpa using this
    have h4 : J ((1 + E) (D' (Ps (Fs x)))) = D' (Ps (Fs x)) := by
      have := congrArg (fun f => f (D' (Ps (Fs x)))) hJ1
      simpa using this
    simp only [comp_apply, ContinuousLinearEquiv.coe_coe]
    calc Fs x = Ps.symm (Ps (Fs x)) := (Ps.symm_apply_apply _).symm
      _ = Ps.symm (D (D' (Ps (Fs x)))) := by rw [h2]
      _ = Ps.symm (D (J ((1 + E) (D' (Ps (Fs x)))))) := by rw [h4]
      _ = Ps.symm (D (J (C (T (D (D' (Ps (Fs x)))))))) := by rw [h3]
      _ = Ps.symm (D (J (C (T (Ps (Fs x)))))) := by rw [h2]
      _ = Ps.symm (D (J (C (Pt (Ft (S x)))))) := by rw [h1]
  · have hJ0 : 0 ≤ 1 / (1 - ‖E‖) := by
      apply div_nonneg zero_le_one; linarith
    calc ‖(Ps.symm : U →L[ℂ] U) ∘L D ∘L J ∘L C ∘L Pt‖
        ≤ ‖(Ps.symm : U →L[ℂ] U)‖ * ‖D ∘L J ∘L C ∘L Pt‖ := opNorm_comp_le _ _
      _ ≤ ‖(Ps.symm : U →L[ℂ] U)‖ * (‖D‖ * ‖J ∘L C ∘L Pt‖) := by
          gcongr; exact opNorm_comp_le _ _
      _ ≤ ‖(Ps.symm : U →L[ℂ] U)‖ * (‖D‖ * (‖J‖ * ‖C ∘L Pt‖)) := by
          gcongr; exact opNorm_comp_le _ _
      _ ≤ ‖(Ps.symm : U →L[ℂ] U)‖ * (‖D‖ * (‖J‖ * (‖C‖ * ‖Pt‖))) := by
          gcongr; exact opNorm_comp_le _ _
      _ ≤ ‖(Ps.symm : U →L[ℂ] U)‖ * (‖D‖ * ((1 / (1 - ‖E‖)) * (‖C‖ * ‖Pt‖))) := by
          gcongr
      _ = _ := by ring

/-- The paper's normal form `F_s = 2^γ · B' F_t A'` with `‖A'‖, ‖B'‖ ≤ 1`, here with
`γ = γ₁ + 2` when `‖S‖ ≤ 2`, `‖D‖ ≤ 2^γ₁`, `‖E‖ ≤ 1/2`, and the three selection
maps have norm at most one. -/
theorem normal_form (Fs : U →L[ℂ] U) (Ft : W →L[ℂ] W) (S T : U →L[ℂ] W) (Ps : U ≃L[ℂ] U)
    (Pt : W →L[ℂ] W) (C : W →L[ℂ] U) (D D' E : U →L[ℂ] U) (γ₁ : ℕ)
    (hres : T ∘L (Ps : U →L[ℂ] U) ∘L Fs = Pt ∘L Ft ∘L S)
    (hN : C ∘L T ∘L D = 1 + E) (hE : ‖E‖ ≤ 1 / 2) (hD : D ∘L D' = 1)
    (hS : ‖S‖ ≤ 2) (hDn : ‖D‖ ≤ 2 ^ γ₁) (hPs : ‖(Ps.symm : U →L[ℂ] U)‖ ≤ 1)
    (hC : ‖C‖ ≤ 1) (hPt : ‖Pt‖ ≤ 1) :
    ∃ A' : U →L[ℂ] W, ∃ B' : W →L[ℂ] U,
      Fs = ((2 : ℂ) ^ (γ₁ + 2)) • (B' ∘L Ft ∘L A') ∧ ‖A'‖ ≤ 1 ∧ ‖B'‖ ≤ 1 := by
  have hE' : ‖E‖ < 1 := by linarith
  obtain ⟨A, B, hFs, hA, hB⟩ := assemble Fs Ft S T Ps Pt C D D' E hres hN hE' hD
  have hinv : 1 / (1 - ‖E‖) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hBn : ‖B‖ ≤ 2 ^ (γ₁ + 1) := by
    have h0 : 0 ≤ ‖(Ps.symm : U →L[ℂ] U)‖ * ‖D‖ := by positivity
    have hE0 : 0 ≤ 1 / (1 - ‖E‖) := by apply div_nonneg zero_le_one; linarith
    calc ‖B‖ ≤ ‖(Ps.symm : U →L[ℂ] U)‖ * ‖D‖ * (1 / (1 - ‖E‖)) * ‖C‖ * ‖Pt‖ := hB
      _ ≤ 1 * 2 ^ γ₁ * 2 * 1 * 1 := by gcongr
      _ = 2 ^ (γ₁ + 1) := by ring
  have h2 : ‖(2 : ℂ)‖ = 2 := RCLike.norm_two
  refine ⟨(2 : ℂ)⁻¹ • A, ((2 : ℂ) ^ (γ₁ + 1))⁻¹ • B, ?_, ?_, ?_⟩
  · rw [hFs]
    ext x
    simp only [smul_apply, comp_apply, map_smul, smul_smul]
    convert (one_smul ℂ (B (Ft (A x)))).symm using 2
    field_simp
    ring
  · rw [norm_smul, norm_inv, h2]
    calc 2⁻¹ * ‖A‖ ≤ 2⁻¹ * 2 := by gcongr; exact hA.trans hS
      _ = 1 := by norm_num
  · rw [norm_smul, norm_inv, norm_pow, h2]
    calc (2 ^ (γ₁ + 1))⁻¹ * ‖B‖ ≤ (2 ^ (γ₁ + 1))⁻¹ * 2 ^ (γ₁ + 1) := by gcongr
      _ = 1 := by field_simp

end Assembly

section Coordinates

variable {s t : ℕ}

/-- The diagonal map `x ↦ (d i * x i)` on `Fin s → ℂ`. -/
noncomputable def diagCLM (d : Fin s → ℂ) : (Fin s → ℂ) →L[ℂ] (Fin s → ℂ) :=
  pi fun i => d i • proj i

@[simp] theorem diagCLM_apply (d : Fin s → ℂ) (x : Fin s → ℂ) (i : Fin s) :
    diagCLM d x i = d i * x i := by
  simp [diagCLM]

/-- Coordinate selection `x ↦ (x (f i))`, covering permutations and row deletion. -/
noncomputable def selectCLM (f : Fin s → Fin t) : (Fin t → ℂ) →L[ℂ] (Fin s → ℂ) :=
  pi fun i => proj (f i)

@[simp] theorem selectCLM_apply (f : Fin s → Fin t) (x : Fin t → ℂ) (i : Fin s) :
    selectCLM f x i = x (f i) := by
  simp [selectCLM]

theorem opNorm_diag_le (d : Fin s → ℂ) {M : ℝ} (hM : 0 ≤ M) (hd : ∀ i, ‖d i‖ ≤ M) :
    ‖diagCLM d‖ ≤ M := by
  refine opNorm_le_bound _ hM fun x => ?_
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [diagCLM_apply, norm_mul]
  exact mul_le_mul (hd i) (norm_le_pi_norm x i) (norm_nonneg _) hM

theorem opNorm_select_le (f : Fin s → Fin t) : ‖selectCLM f‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun x => ?_
  rw [pi_norm_le_iff_of_nonneg (by positivity), one_mul]
  intro i
  rw [selectCLM_apply]
  exact norm_le_pi_norm x (f i)

/-- Diagonal maps with nonvanishing entries are invertible by the reciprocal diagonal. -/
theorem diagCLM_comp_inv (d : Fin s → ℂ) (hd : ∀ i, d i ≠ 0) :
    diagCLM d ∘L diagCLM (fun i => (d i)⁻¹) = 1 := by
  ext x i
  simp [mul_inv_cancel_left₀ (hd i)]

end Coordinates

end IntegerMultBounds.NLogN
