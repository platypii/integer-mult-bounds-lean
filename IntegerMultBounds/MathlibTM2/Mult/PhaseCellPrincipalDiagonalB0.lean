module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedIntervalTransfer
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedB0Endpoint
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTargetCoreLocalAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrincipalTargetOwnedOutput
public import IntegerMultBounds.NLogN.PhaseCellCyclicPrincipalGeometry

/-! Compare the executed principal-diagonal packet with the exact B0 target.
Locality and matrix perturbation change only its certificate, never its bytes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership PhaseCellInterface
variable {s t p u l q : ℕ} [NeZero s] {α gap : ℝ}

theorem componentSolution_target_owned_global
    (axis : RecoveryAxisBounds s t p u l α gap) (hpq : p+1 ≤ q)
    (L k localityTarget : ℕ)
    (ha : localityDepth p localityTarget*PhaseCellBand.width p u ≤ cut s t L k)
    (hb : cut s t L (k+1)+localityDepth p localityTarget*PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod t → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hy : ∀ F ∈ complexComponentFields (selectedRhsFields s Fs), SchurDominance.Solves
      (realMatrix s t p u)
      (cyclicPrincipalVertices s (cut s t L k-localityDepth p localityTarget*PhaseCellBand.width p u)
        (rows s t L k+2*(localityDepth p localityTarget*PhaseCellBand.width p u)))
      (y F) (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re)) :
    ∀ F ∈ Fs, ErrorOn (haloVertices s (cut s t L k) (cut s t L (k+1)))
      (componentSolution y (fun i => F (rowIndex s t i))) (axis.globalHalfGridTarget F)
      (2/(2 : ℝ)^localityTarget) := by
  have hprincipal := cyclicPrincipalVertices_owned L k
    (localityDepth p localityTarget*PhaseCellBand.width p u) ha hb
  intro F hmem
  have hselected : (fun i => F (rowIndex s t i)) ∈ selectedRhsFields s Fs :=
    List.mem_map.mpr ⟨F,hmem,rfl⟩
  have hre := hy _ (List.mem_append_left _ (List.mem_map.mpr ⟨_,hselected,rfl⟩))
  have him := hy _ (List.mem_append_right _ (List.mem_map.mpr ⟨_,hselected,rfl⟩))
  have hsol := componentSolution_solves q (q-p-1) _ _ y (fun i => F (rowIndex s t i)) hre him
  have hq : p+1+(q-p-1) = q := by omega
  have hhalf (i : ZMod s) : value q ((2 : GaussianInt)^(q-p-1)*F (rowIndex s t i)) =
      (1/2 : ℂ)*value p (F (rowIndex s t i)) := by
    have hh := halfGrid_value p (q-p-1) (F (rowIndex s t i))
    rw [hq] at hh
    exact hh
  simp_rw [hhalf,hprincipal] at hsol
  have hglobal := axis.globalHalfGridTarget_solves F
  have hrhs (i : ZMod s) : ‖(1/2 : ℂ)*value p (F (rowIndex s t i))‖ ≤ 1 := by
    rw [norm_mul]
    have hh := hF F hmem (rowIndex s t i)
    norm_num
    linarith
  have hlocal (x z rhs : ZMod s → ℝ)
      (hx : SchurDominance.Solves (realMatrix s t p u) Finset.univ x rhs)
      (hz : SchurDominance.Solves (realMatrix s t p u)
        (haloVertices s (cut s t L k-localityDepth p localityTarget*PhaseCellBand.width p u)
          (cut s t L (k+1)+localityDepth p localityTarget*PhaseCellBand.width p u)) z rhs)
      (hrhs : ∀ i, |rhs i| ≤ 1) :
      ErrorOn (haloVertices s (cut s t L k) (cut s t L (k+1))) z x (1/(2 : ℝ)^localityTarget) := by
    have hh := ErrorOn.target_owned_global axis.hst axis.hα p u localityTarget L k axis.hp
      axis.hpacket axis.hαu axis.hθ axis.hgap axis.hbudget ha hb z x z rhs 0 hx hz hrhs
      (by intro i hi; simp)
    simpa only [zero_add] using hh
  have hr := hlocal _ _ _ hglobal.1 hsol.1 (fun i => (Complex.abs_re_le_norm _).trans (hrhs i))
  have hi := hlocal _ _ _ hglobal.2 hsol.2 (fun i => (Complex.abs_im_le_norm _).trans (hrhs i))
  intro i hmemI
  have hn := Complex.norm_le_abs_re_add_abs_im
    (componentSolution y (fun i => F (rowIndex s t i)) i-axis.globalHalfGridTarget F i)
  simp only [Complex.sub_re,Complex.sub_im] at hn
  have he := hn.trans (add_le_add (hr i hmemI) (hi i hmemI))
  convert he using 1
  ring

theorem principalDiagonal_target_owned_B0_error {alpha : ℕ} [NeZero t]
    (axis : RecoveryAxisBounds s t p u l (alpha : ℝ) gap) (hpq : p+1 ≤ q)
    (L k localityTarget : ℕ)
    (ha : localityDepth p localityTarget*PhaseCellBand.width p u ≤ cut s t L k)
    (hb : cut s t L (k+1)+localityDepth p localityTarget*PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod t → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hy : ∀ F ∈ complexComponentFields (selectedRhsFields s Fs), SchurDominance.Solves
      (realMatrix s t p u)
      (cyclicPrincipalVertices s (cut s t L k-localityDepth p localityTarget*PhaseCellBand.width p u)
        (rows s t L k+2*(localityDepth p localityTarget*PhaseCellBand.width p u)))
      (y F) (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re))
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t (alpha : ℝ) = 1) :
    ∀ F ∈ Fs, ErrorOn (haloVertices s (cut s t L k) (cut s t L (k+1)))
      (fun i => (dPrime s t (alpha : ℝ) i : ℂ)*(((2 : ℂ)^inverseNormalizationShift p)⁻¹*
        componentSolution y (fun i => F (rowIndex s t i)) i))
      (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*resampB₀ s t (alpha : ℝ) J (fun i => value p (F i)) i)
      ((2/(2 : ℝ)^localityTarget)/(2 : ℝ)^inverseNormalizationShift p+
        (((32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2)/(2 : ℝ)^inverseNormalizationShift p)) := by
  intro F hmem
  have he := componentSolution_target_owned_global axis hpq L k localityTarget ha hb Fs hF y hy F hmem
  have hscaled : ErrorOn (haloVertices s (cut s t L k) (cut s t L (k+1)))
      (fun i => (dPrime s t (alpha : ℝ) i : ℂ)*(((2 : ℂ)^inverseNormalizationShift p)⁻¹*
        componentSolution y (fun i => F (rowIndex s t i)) i))
      (fun i => (dPrime s t (alpha : ℝ) i : ℂ)*(((2 : ℂ)^inverseNormalizationShift p)⁻¹*
        axis.globalHalfGridTarget F i)) ((2/(2 : ℝ)^localityTarget)/(2 : ℝ)^inverseNormalizationShift p) := by
    intro i hi
    have hd : ‖(dPrime s t (alpha : ℝ) i : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (dPrime_nonneg i)]
      exact dPrime_le_one i
    rw [←mul_sub,←mul_sub,norm_mul,norm_mul,norm_inv,norm_pow,Complex.norm_ofNat,←mul_assoc]
    calc
      _ ≤ 1*((2 : ℝ)^inverseNormalizationShift p)⁻¹*(2/(2 : ℝ)^localityTarget) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hd (by positivity)) (he i hi) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  exact hscaled.trans (fun i _ => axis.globalHalfGridTarget_B0_error (inverseNormalizationShift p)
    J hJ F (hF F hmem) i (Finset.mem_univ i))

theorem PackedIntervalOutput.target_owned_B0 {alpha : ℕ} [NeZero t]
    (axis : RecoveryAxisBounds s t p u l (alpha : ℝ) gap) (hpq : p+1 ≤ q)
    (L k localityTarget : ℕ)
    (ha : localityDepth p localityTarget*PhaseCellBand.width p u ≤ cut s t L k)
    (hb : cut s t L (k+1)+localityDepth p localityTarget*PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod t → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hy : ∀ F ∈ complexComponentFields (selectedRhsFields s Fs), SchurDominance.Solves
      (realMatrix s t p u)
      (cyclicPrincipalVertices s (cut s t L k-localityDepth p localityTarget*PhaseCellBand.width p u)
        (rows s t L k+2*(localityDepth p localityTarget*PhaseCellBand.width p u)))
      (y F) (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re))
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t (alpha : ℝ) = 1)
    {A W : ℕ} {arithmetic : ℝ} {word : List (Fin (A+4))}
    (h : PackedIntervalOutput p W (cut s t L k) (rows s t L k)
      (((selectedRhsFields s Fs).map (fun F i =>
        ((2 : ℂ)^inverseNormalizationShift p)⁻¹*componentSolution y F i)).reverse.map
        (fun z i => (dPrime s t (alpha : ℝ) i : ℂ)*z i)) arithmetic word) :
    PackedIntervalOutput p W (cut s t L k) (rows s t L k)
      (Fs.reverse.map (fun F i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*
        resampB₀ s t (alpha : ℝ) J (fun i => value p (F i)) i))
      (arithmetic+((2/(2 : ℝ)^localityTarget)/(2 : ℝ)^inverseNormalizationShift p+
        (((32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2)/(2 : ℝ)^inverseNormalizationShift p))) word := by
  have hrows : cut s t L k+rows s t L k = cut s t L (k+1) := by
    have hm := cut_mono s t L (show k ≤ k+1 by omega)
    unfold rows
    omega
  apply h.transfer
  simp only [hrows,selectedRhsFields,List.map_map,Function.comp_def,List.map_reverse]
  apply List.forall₂_reverse_iff.mpr
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  rw [List.forall₂_same]
  exact principalDiagonal_target_owned_B0_error axis hpq L k localityTarget ha hb Fs hF y hy J hJ

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
