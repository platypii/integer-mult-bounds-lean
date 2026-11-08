module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedB0Locality
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplexB0Endpoint

/-! Identify the constructed half-grid target with the manuscript B0 inverse target. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RecoveryAxisBounds
open IntegerMultBounds IntegerMultBounds.NLogN ContinuousLinearMap
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface IntegerMultBounds.MathlibTM2.Mult.FastB0
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.NLogN.PhaseCellMatrix
variable {s t p u l : ℕ} [NeZero s] [NeZero t] {alpha gap : ℝ}

omit [NeZero t] in
theorem globalHalfGridTarget_eq_inverse (h : RecoveryAxisBounds s t p u l alpha gap)
    (L : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hL : L ∘L PhaseCellOperator.rounded s t p u = 1)
    (F : ZMod t → GaussianInt) :
    h.globalHalfGridTarget F = L ((1/2 : ℂ) • rowSelect s t (fun i => value p (F i))) := by
  have hs := h.globalHalfGridTarget_solves F
  apply (inverse_parts p u L hL _ (fun i => (h.globalHalfGridTarget F i).re)
    (fun i => (h.globalHalfGridTarget F i).im) ?_ ?_).symm
  · funext i
    simpa only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,rowSelect]
      using hs.1 i (Finset.mem_univ i)
  · funext i
    simpa only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,rowSelect]
      using hs.2 i (Finset.mem_univ i)

theorem globalHalfGridTarget_inverse_error (h : RecoveryAxisBounds s t p u l alpha gap)
    (j : ℕ) (J L : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hL : L ∘L PhaseCellOperator.rounded s t p u = 1) (delta : ℝ) (hdiff : ‖L-J‖ ≤ delta)
    (F : ZMod t → GaussianInt) (hF : ∀ i, ‖value p (F i)‖ ≤ 1) :
    ErrorOn Finset.univ (fun i => (dPrime s t alpha i : ℂ)*(((2 : ℂ)^j)⁻¹*h.globalHalfGridTarget F i))
      (fun i => ((2 : ℂ)^j)⁻¹*resampB₀ s t alpha J (fun i => value p (F i)) i)
      ((delta/2)/(2 : ℝ)^j) := by
  let v := rowSelect s t (fun i => value p (F i))
  let half := (1/2 : ℂ) • v
  have hv : ‖v‖ ≤ 1 := (norm_rowSelect_le _).trans ((pi_norm_le_iff_of_nonneg zero_le_one).mpr hF)
  have hhalf : ‖half‖ ≤ 1/2 := by
    rw [show half = (1/2 : ℂ) • v from rfl,norm_smul]
    norm_num
    linarith
  have hdelta : 0 ≤ delta := (norm_nonneg _).trans hdiff
  intro i _
  have hX : h.globalHalfGridTarget F i = L half i := congrFun (h.globalHalfGridTarget_eq_inverse L hL F) i
  have hB : resampB₀ s t alpha J (fun i => value p (F i)) i = (dPrime s t alpha i : ℂ)*J half i := by
    rw [resampB₀_apply]
    simp only [half,map_smul,Pi.smul_apply,smul_eq_mul]
    ring
  have hD : ‖(dPrime s t alpha i : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (dPrime_nonneg i)]
    exact dPrime_le_one i
  have he : ‖(L-J) half i‖ ≤ delta/2 := by
    calc
      _ ≤ ‖(L-J) half‖ := norm_le_pi_norm _ i
      _ ≤ ‖L-J‖*‖half‖ := le_opNorm _ _
      _ ≤ delta*(1/2) := mul_le_mul hdiff hhalf (norm_nonneg _) hdelta
      _ = _ := by ring
  have heq : (dPrime s t alpha i : ℂ)*(((2 : ℂ)^j)⁻¹*h.globalHalfGridTarget F i)-
      ((2 : ℂ)^j)⁻¹*resampB₀ s t alpha J (fun i => value p (F i)) i =
      (dPrime s t alpha i : ℂ)*((2 : ℂ)^j)⁻¹*((L-J) half i) := by
    rw [hX,hB]
    simp only [sub_apply,Pi.sub_apply]
    ring
  rw [heq,norm_mul,norm_mul,norm_inv,norm_pow,Complex.norm_ofNat]
  calc
    _ ≤ 1*((2 : ℝ)^j)⁻¹*(delta/2) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hD (by positivity)) he (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem globalHalfGridTarget_B0_error (h : RecoveryAxisBounds s t p u l alpha gap) (j : ℕ)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t alpha = 1)
    (F : ZMod t → GaussianInt) (hF : ∀ i, ‖value p (F i)‖ ≤ 1) :
    ErrorOn Finset.univ (fun i => (dPrime s t alpha i : ℂ)*(((2 : ℂ)^j)⁻¹*h.globalHalfGridTarget F i))
      (fun i => ((2 : ℂ)^j)⁻¹*resampB₀ s t alpha J (fun i => value p (F i)) i)
      (((32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2)/(2 : ℝ)^j) := by
  obtain ⟨L,_,hL,hdiff⟩ := rounded_inverse_endpoint h.hst h.hα p u h.hp h.hpacket h.hαu h.hθ h.hgap h.hbudget J hJ
  exact h.globalHalfGridTarget_inverse_error j J L hL _ hdiff F hF

theorem globalHalfGridTarget_B0_accuracy {D : Type} (h : RecoveryAxisBounds s t p u l alpha gap) (j : ℕ)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t alpha = 1)
    (core : Finset (ZMod s)) (Fs : List (ZMod t → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (Ds : List D) (out : D → ZMod s → ℂ) (arithmetic : ℝ)
    (hgood : List.Forall₂ (fun F d => ErrorOn core (out d)
      (fun i => (dPrime s t alpha i : ℂ)*(((2 : ℂ)^j)⁻¹*h.globalHalfGridTarget F i)) arithmetic) Fs Ds) :
    List.Forall₂ (fun F d => ErrorOn core (out d)
      (fun i => ((2 : ℂ)^j)⁻¹*resampB₀ s t alpha J (fun i => value p (F i)) i)
      (arithmetic+((32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2)/(2 : ℝ)^j)) Fs Ds := by
  have hm := (List.forall₂_and_left Fs Ds).mpr ⟨fun F hmem => hmem,hgood⟩
  apply List.Forall₂.imp _ hm
  intro F d hpair
  exact hpair.2.trans (fun i _ => h.globalHalfGridTarget_B0_error j J hJ F (hF F hpair.1) i (Finset.mem_univ i))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RecoveryAxisBounds
