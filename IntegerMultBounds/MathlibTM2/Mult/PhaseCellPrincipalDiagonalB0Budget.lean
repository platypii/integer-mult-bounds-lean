module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrincipalDiagonalB0
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedIntervalDiagonal
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridB0Budget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPublishedOperator

/-! Linear precision gives nine units of p-bit batch error and unit-ball
preservation for the signed fields already encoded in the output packet. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface IntegerMultBounds.MathlibTM2.Mult.FastB0

theorem principalDiagonalB0_error_le_nine {p target localityTarget j : ℕ}
    (hp : 4 ≤ p) (htarget : p+2 ≤ target) (hlocality : p+2 ≤ localityTarget) :
    (6/(2 : ℝ)^p+(2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^j))+
      ((2/(2 : ℝ)^localityTarget)/(2 : ℝ)^j+
        (((32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2)/(2 : ℝ)^j)) ≤ 9/(2 : ℝ)^p := by
  let m := min target localityTarget
  have hcore := generatedCore_error_le_quarters (j := j) (p := p) (target := m) (by omega)
  have ht : (1/(2 : ℝ)^target)/(2 : ℝ)^j ≤ (1/(2 : ℝ)^m)/(2 : ℝ)^j :=
    div_le_div_of_nonneg_right (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (Nat.min_le_left _ _))) (by positivity)
  have hl : (1/(2 : ℝ)^localityTarget)/(2 : ℝ)^j ≤ (1/(2 : ℝ)^m)/(2 : ℝ)^j :=
    div_le_div_of_nonneg_right (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (Nat.min_le_right _ _))) (by positivity)
  have hmix : (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^j)+
      (2/(2 : ℝ)^localityTarget)/(2 : ℝ)^j ≤ (11/4 : ℝ)/(2 : ℝ)^p := by
    have heq : (2/(2 : ℝ)^localityTarget)/(2 : ℝ)^j =
        (1/(2 : ℝ)^localityTarget)/(2 : ℝ)^j+(1/(2 : ℝ)^localityTarget)/(2 : ℝ)^j := by ring
    have heqM : (1/(2 : ℝ)^m+1/(2 : ℝ)^m)/(2 : ℝ)^j =
        (1/(2 : ℝ)^m)/(2 : ℝ)^j+(1/(2 : ℝ)^m)/(2 : ℝ)^j := by ring
    rw [heq]
    rw [heqM] at hcore
    linarith only [ht,hl,hcore]
  have hm := gridInverse_matrix_error_le_quarter hp
  have hmatrix : ((32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2) ≤ (1/4 : ℝ)/(2 : ℝ)^p := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2^p)).mpr
    nlinarith only [hm]
  have hscaled : (((32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2)/(2 : ℝ)^j) ≤ (1/4 : ℝ)/(2 : ℝ)^p :=
    (div_le_self (by positivity) (one_le_pow₀ (by norm_num))).trans hmatrix
  have hsum := add_le_add hmix hscaled
  calc
    _ = 6/(2 : ℝ)^p+((2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^j)+
      (2/(2 : ℝ)^localityTarget)/(2 : ℝ)^j+(((32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2)/(2 : ℝ)^j)) := by ring
    _ ≤ 6/(2 : ℝ)^p+((11/4 : ℝ)/(2 : ℝ)^p+(1/4 : ℝ)/(2 : ℝ)^p) := add_le_add (le_refl _) hsum
    _ = _ := by ring

theorem diagonalB0_error_small {p : ℕ} (hp : 5 ≤ p) : (9 : ℝ)/2^p ≤ 1/2 := by
  have hpow : (32 : ℝ) ≤ 2^p := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp
    norm_num at hh
    exact hh
  exact (div_le_iff₀ (by positivity)).mpr (by linarith only [hpow])

theorem normalizedB0_norm_le_half {s t : ℕ} [NeZero s] [NeZero t] (p : ℕ) (α : ℝ)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : ‖J‖ ≤ 4*(p : ℝ))
    (v : ZMod t → ℂ) (hv : ‖v‖ ≤ 1) (i : ZMod s) :
    ‖((2 : ℂ)^inverseNormalizationShift p)⁻¹*resampB₀ s t α J v i‖ ≤ (1/2 : ℝ) := by
  let normalized := ((2 : ℂ)^inverseNormalizationShift p)⁻¹ • ((1/2 : ℂ) • J)
  have hn : ‖normalized (rowSelect s t v)‖ ≤ (1/2 : ℝ) := by
    have hop := normalizedInverse_norm_le_half p J hJ
    have hinput := (norm_rowSelect_le (s := s) v).trans hv
    calc
      _ ≤ ‖normalized‖*‖rowSelect s t v‖ := normalized.le_opNorm _
      _ ≤ (1/2 : ℝ)*1 := mul_le_mul hop hinput (norm_nonneg _) (by norm_num)
      _ = 1/2 := by ring
  have heq : ((2 : ℂ)^inverseNormalizationShift p)⁻¹*resampB₀ s t α J v i =
      (dPrime s t α i : ℂ)*normalized (rowSelect s t v) i := by
    rw [resampB₀_apply]
    simp only [normalized,smul_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hd : ‖(dPrime s t α i : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (dPrime_nonneg i)]
    exact dPrime_le_one i
  rw [heq,norm_mul]
  exact (mul_le_mul_of_nonneg_right hd (norm_nonneg _)).trans
    (by simpa only [one_mul] using (norm_le_pi_norm (normalized (rowSelect s t v)) i).trans hn)

theorem PackedIntervalOutput.b0_unit_fields {A s t p u l W start rows : ℕ}
    [NeZero s] [NeZero t] {α gap : ℝ}
    (axis : RecoveryAxisBounds s t p u l α gap) (hp : 5 ≤ p)
    (hA : 4 ≤ A) (hW : p+3 ≤ W) (hfit : start+rows ≤ s)
    (Fs : List (ZMod t → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t α = 1)
    {error : ℝ} {word : List (Fin (A+4))} (he : error ≤ 9/(2 : ℝ)^p)
    (h : PackedIntervalOutput p W start rows
      (Fs.reverse.map (fun F i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*
        resampB₀ s t α J (fun i => value p (F i)) i)) error word) :
    PackedUnitIntervalOutput p W start rows
      (Fs.reverse.map (fun F i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*
        resampB₀ s t α J (fun i => value p (F i)) i)) (9/(2 : ℝ)^p) word := by
  obtain ⟨L,hJn,hLH,hdiff⟩ := rounded_inverse_endpoint axis.hst axis.hα p u axis.hp axis.hpacket
    axis.hαu axis.hθ axis.hgap axis.hbudget J hJ
  have hmag : ∀ z ∈ Fs.reverse.map (fun F i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*
      resampB₀ s t α J (fun i => value p (F i)) i),
      ∀ i ∈ haloVertices s start (start+rows), ‖z i‖ ≤ (1/2 : ℝ) := by
    intro z hz i hi
    obtain ⟨F,hmem,rfl⟩ := List.mem_map.mp hz
    exact normalizedB0_norm_le_half p α J hJn _
      ((pi_norm_le_iff_of_nonneg zero_le_one).mpr (hF F (List.mem_reverse.mp hmem))) i
  have hsmall := diagonalB0_error_small hp
  obtain ⟨Ds,hlen,hword,hfits,hgood⟩ := (h.mono he).signed_fields hA hW hfit (1/2) 1
    (by linarith only [hsmall]) (by norm_num) hmag
  exact ⟨Ds,hlen,hword,hfits,hgood⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
