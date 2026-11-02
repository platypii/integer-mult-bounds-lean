module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDyadicRouteCharge
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeometryControlSizing
public import IntegerMultBounds.NLogN.PhaseCellCoreGatherCount

/-! Comparable full-core key widths yield the manuscript's dimension-times-axis
routing charge. The selected core-width upper bound remains an explicit gate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz IntegerMultBounds.NLogN.PhaseCellMatrix

theorem dyadicRouteCharge_le_dimension (a b d ell : ℕ)
    (ha : a ≤ d*ell) (hb : b ≤ ell) (hell : ell ≤ 2*b) (hsmall : ell ≤ 16*d^2) :
    dyadicRouteCharge a b ≤ 18*d*((ell : ℝ)^Parameters.tau+1) := by
  have hcharge := dyadicRouteCharge_le_axis a b d ell ha hb hell
  by_cases hz : ell = 0
  · have hb0 : b = 0 := by omega
    simp [dyadicRouteCharge,hb0]
    positivity
  · have hell1 : (1 : ℝ) ≤ ell := by exact_mod_cast (by omega : 1 ≤ ell)
    have hpow := Real.rpow_le_rpow_of_exponent_le hell1
      (show (1 : ℝ) ≤ Parameters.tau*2 by norm_num [Parameters.tau])
    rw [Real.rpow_one,Real.rpow_mul (Nat.cast_nonneg ell),Real.rpow_two] at hpow
    have hsmallR : (ell : ℝ) ≤ 16*d^2 := by exact_mod_cast hsmall
    have hsq := mul_le_mul_of_nonneg_left hsmallR (Nat.cast_nonneg ell : (0 : ℝ) ≤ ell)
    have hp := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ 16*(d : ℝ)^2)
    have hprod : (0 : ℝ) ≤ (d : ℝ)*(ell : ℝ)^Parameters.tau := by positivity
    have hlinear : (ell : ℝ) ≤ 4*d*(ell : ℝ)^Parameters.tau := by nlinarith only [hsq,hp,hprod]
    nlinarith only [hcharge,hlinear,(show (0 : ℝ) ≤ d from Nat.cast_nonneg d)]

theorem selectedAxisLog_le_dimension_sq {n : ℕ} (h : Sizes.Big n) : Sizes.ℓ n ≤ 16*(Sizes.d n)^2 := by
  have hp := selectedPrecision_le_dimension_cube h
  have hl := h.ℓ_bounds.2
  have hd := h.one_le_d
  by_contra hc
  have hlt : 16*(Sizes.d n)^2+1 ≤ Sizes.ℓ n := by omega
  have hm := Nat.mul_le_mul_left (3*Sizes.d n) hlt
  nlinarith only [hm,hl,hp,hd]

theorem selectedFullCoreRouteCharge_le {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n))
    (a width radius : ℕ) (ha : a ≤ Sizes.d n*Sizes.ℓ n) (hw : 0 < width) (hr : radius ≤ width)
    (hquot : 2^((Sizes.ℓ n+1)/2)+2 ≤ Sizes.s n i/width) :
    dyadicRouteCharge a (Nat.clog 2 (coreGatherIndices (Sizes.s n i) width radius (width+2*radius)).length) ≤
      18*Sizes.d n*((Sizes.ℓ n : ℝ)^Parameters.tau+1) := by
  have hs : Sizes.s n i ≤ 2^Sizes.ℓ n := by
    have hst := (h.good.lt i).le
    have ht : Sizes.t n i ≤ 2^Sizes.ℓ n := by
      unfold Sizes.t
      split_ifs
      · exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
      · rfl
    exact hst.trans ht
  obtain ⟨hb,hell⟩ := fullCoreGather_clog_bounds (Sizes.s n i) width radius (Sizes.ℓ n) hw hr hs hquot
  exact dyadicRouteCharge_le_dimension _ _ _ _ ha hb hell (selectedAxisLog_le_dimension_sq h)

/-- Both generated length classes have the same charge bound. The clipped
class has at most one core, hence no dyadic routing stages. -/
theorem selectedCoreGroupRouteCharge_le {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n))
    (a width radius L : ℕ) (ha : a ≤ Sizes.d n*Sizes.ℓ n) (hw : 0 < width) (hr : radius ≤ width)
    (hquot : 2^((Sizes.ℓ n+1)/2)+2 ≤ Sizes.s n i/width)
    (hL : L ∈ coreGatherLengths (Sizes.s n i) width radius) :
    dyadicRouteCharge a (Nat.clog 2 (coreGatherIndices (Sizes.s n i) width radius L).length) ≤
      18*Sizes.d n*((Sizes.ℓ n : ℝ)^Parameters.tau+1) := by
  simp only [coreGatherLengths,List.mem_dedup,List.mem_cons,List.not_mem_nil,or_false] at hL
  rcases hL with rfl | rfl
  · exact selectedFullCoreRouteCharge_le h i a width radius ha hw hr hquot
  · have hcount := clippedCoreGather_length_le_one (Sizes.s n i) width radius hw
    have hzero := Nat.clog_of_right_le_one hcount 2
    rw [hzero]
    simp only [dyadicRouteCharge,ite_true]
    positivity

end IntegerMultBounds.MathlibTM2.Cost
