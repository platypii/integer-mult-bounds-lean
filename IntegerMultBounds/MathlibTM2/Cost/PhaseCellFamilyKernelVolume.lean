module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyCouplingFast

/-! Actual boundary rows and coupling nonzeros give the phase-gap work budget.
No boundary rank is identified with tensor dimension. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem familyKernelVolume_le {s t band a b : ℕ} [NeZero s] (hst : s < t) (hband : 1 ≤ band) :
    familyKernelVolume s t band a b ≤ 200*(t+(t-s)*band^2) := by
  let g := t-s
  let N := (haloBoundary s t band a b).card
  let active := haloBoundaryCountBound s t (2*band) a b+4*band
  have hg : 1 ≤ g := by dsimp only [g]; omega
  have hg2 : g+2 ≤ 3*g := by omega
  have hN : N ≤ 2*band*(g+2) :=
    (haloBoundary_card_bound hst band a b).trans (Nat.min_le_right _ _)
  have hN' : N ≤ 6*band*g := by
    have h := Nat.mul_le_mul_left (2*band) hg2
    nlinarith only [hN,h]
  have hpos : 1 ≤ band*g := Nat.mul_pos hband hg
  have hNplus : N+1 ≤ 7*band*g := by nlinarith only [hN',hpos]
  have hW : 12*band+1 ≤ 13*band := by omega
  have hrows := Nat.mul_le_mul hNplus hW
  have ha : active ≤ 4*band*(g+2)+4*band := by
    have h := Nat.min_le_right (b-a) (2*(2*band)*(g+2))
    change min (b-a) (2*(2*band)*(g+2))+4*band ≤ 4*band*(g+2)+4*band
    nlinarith only [h]
  have hbg : band ≤ band*g := Nat.le_mul_of_pos_right _ hg
  have ha' : active ≤ 16*band*g := by
    have h := Nat.mul_le_mul_left (4*band) hg2
    nlinarith only [ha,h,hbg]
  have hL : 2*band+1 ≤ 3*band := by omega
  have hwork := Nat.mul_le_mul ha' hL
  change t+(N+1)*(12*band+1)+s+active*(2*band+1) ≤ 200*(t+g*band^2)
  have hst' : s ≤ t := by omega
  nlinarith only [hrows,hwork,hst',Nat.zero_le t,Nat.zero_le (g*band^2)]

/-- All interior, boundary and coupling kernels obey the derived gap-volume budget. -/
theorem familyComplexGeometry_selected_gap_fast_le (ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p u target s t a b : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → PhaseCellBand.width p u ≤ s →
      1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1 → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p →
      let l := haloInverseRingLog s t
      (generatedFamilyComplexGeometryLineCost p u l s t a b target : ℝ) ≤
        (familyComplexControlRemainingCost p u l s t a b target : ℝ)+
          C*((t+(t-s)*(PhaseCellBand.width p u)^2 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := familyComplexGeometry_selected_kernel_fast_le ct cG
  refine ⟨200*C,by positivity,?_⟩
  intro p u target s t a b _ hp hst hband hθ ht hgeometry
  have h := hfast p u target s t a b hp hst hband hθ ht hgeometry
  have hvolume := familyKernelVolume_le (a := a) (b := b) hst (PhaseCellBand.width_pos p u)
  have hv : (familyKernelVolume s t (PhaseCellBand.width p u) a b : ℝ) ≤
      200*((t+(t-s)*(PhaseCellBand.width p u)^2 : ℕ) : ℝ) := by exact_mod_cast hvolume
  have hMp : 0 ≤ (p : ℝ)^(129/128 : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hC) hMp
  nlinarith only [h,hscaled]

end IntegerMultBounds.MathlibTM2.Cost
