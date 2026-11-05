module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellAmortizedCoreGeometry
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellHaloRingSizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseCallerSizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCommonWidth

/-! Selected dimensions supply the raw caller's mathematical geometry once.
The caller still supplies physical storage and numerical input hypotheses. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

structure RawCallerGeometry (p u s t width radius l B W : ℕ) : Prop where
  precision : 4 ≤ p
  source_lt_target : s < t
  phaseGap : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1
  band_le : PhaseCellBand.width p u ≤ s
  padding : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1
  coreRoom : 3*width < s
  radius_pos : 0 < radius
  radius_le : radius ≤ width
  geometryFits : s+width+2*radius < 2^B
  outputWidth : 2*p+13 ≤ W

theorem selectedRawCallerGeometry (ct : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ u target : ℕ, target ≤ ct*Sizes.p n →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      RawCallerGeometry p u s t (amortizedCoreWidth ct p)
        (localityDepth p target*PhaseCellBand.width p u) l
        (inverseCallerWordWidth p u l target s t) (packedHaloCommonWidth p l s u (target+1) 2) := by
  filter_upwards [selectedAmortizedCoreGeometry ct] with n hn
  intro h i _ u target htarget p s t l
  have hp : 1 ≤ p := by have := h.thirteen_le_p; omega
  obtain ⟨hw,_,hrw,hroom,_⟩ := hn h i u target htarget
  change 3*amortizedCoreWidth ct p+PhaseCellBand.width p u ≤ s at hroom
  change localityDepth p target*PhaseCellBand.width p u ≤ amortizedCoreWidth ct p at hrw
  have hr : 0 < localityDepth p target*PhaseCellBand.width p u := localityCoreWidth_pos hp u target
  have hb := PhaseCellBand.width_pos p u
  have hcore : amortizedCoreWidth ct p ≤ s := by omega
  have hst : s < t := h.good.lt i
  have hwide := (inverseCallerWordWidth_fits p u l target s t).2.1
  have hgeometry : s+amortizedCoreWidth ct p+2*(localityDepth p target*PhaseCellBand.width p u) <
      2^inverseCallerWordWidth p u l target s t := by
    have hscalar : s+amortizedCoreWidth ct p+2*(localityDepth p target*PhaseCellBand.width p u) ≤ 4*s := by
      change localityDepth p target*PhaseCellBand.width p u ≤ amortizedCoreWidth ct p at hrw
      omega
    nlinarith only [hwide,hscalar,hst,Nat.zero_le (t^2)]
  have hword : 2*p+13 ≤ packedHaloCommonWidth p l s u (target+1) 2 := by
    unfold packedHaloCommonWidth executionWidth executionExponent
      inputExponent sourceExponent
    omega
  exact ⟨by have := h.thirteen_le_p; omega,hst,h.quarter_p_le_theta i,
    by omega,haloInverseRingLog_fits s t (PhaseCellBand.width p u),by omega,
    hr,hrw,hgeometry,hword⟩

end IntegerMultBounds.MathlibTM2.Cost
