module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicInteriorGeometry
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRealResidualLedger

/-! The actual windowed residual has a uniform selected polynomial price at
joint cyclic boundary precision, including both numerical calls and lifecycle. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedCyclicWindowedResidual_poly_le (ct : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ u target a span x y : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → x ≤ Sizes.s n i → y ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let N := (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a span).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      (windowedSchurResidualCost p l s t u bits 2 x y : ℝ) ≤
        C*(t : ℝ)^5 := by
  obtain ⟨C,hC,hinterior⟩ := selectedCyclicInteriorConstruction_poly_le ct
  obtain ⟨K,hcoupling⟩ := selectedCyclicCoupling_poly_le ct
  let cw := 1032+8*ct
  let L := 10000*(32775+cw)*(cw+1)
  refine ⟨C+K+L,by positivity,?_⟩
  filter_upwards [hinterior] with n hn
  intro h i _ u target a span x y hu htarget hband hx hy
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let band := PhaseCellBand.width p u
  let N := (cyclicPrincipalBoundary s t band a span).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let stage := initialSchurTarget p u bits 2
  let q := executionPrecision p l stage 2
  let w := executionWidth p l stage 2
  have hi := hn h i u target a span x y hu htarget hband hx hy
  have hc := (Nat.cast_le (α := ℝ)).mpr (hcoupling n h i u target a span x y hu htarget hband hx hy false)
  have hw : w ≤ cw*p := selectedCyclicWorkingWidth_le ct h i u target a span htarget hband
  have hpt : p ≤ t := selectedPrecision_le_axis h i
  have hst : s ≤ t := (h.good.lt i).le
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp [t]; omega
  have hq : q ≤ cw*t := (show q ≤ w by dsimp [q,w,executionPrecision,executionWidth]; omega).trans
    (hw.trans (Nat.mul_le_mul_left cw hpt))
  have hpoly := residualLifecycleCost_poly p q s t u band x y cw ht hpt hq hst
    (hu.trans hpt) (hband.trans hst) (hx.trans hst) (hy.trans hst)
  have hb := (Nat.cast_le (α := ℝ)).mpr (windowedSchurResidualCost_le_numerical p l s t u bits 2 x y)
  have hp4 := (Nat.cast_le (α := ℝ)).mpr (Nat.pow_le_pow_left hpt 4)
  have hscale := mul_le_mul_of_nonneg_left hp4 (by positivity : 0 ≤ C*(t : ℝ))
  have ht5 := (Nat.cast_le (α := ℝ)).mpr (Nat.pow_le_pow_right ht (by decide : 2 ≤ 5))
  have hlife := mul_le_mul_of_nonneg_left ht5 (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  have hr := (Nat.cast_le (α := ℝ)).mpr hpoly
  change _ ≤ ((L*t^2 : ℕ) : ℝ) at hr
  dsimp only [p,s,t,l,band,N,bits,stage,q,w] at hb hr hscale hlife
  push_cast at hb hc hr hp4 hscale hlife
  nlinarith only [hi,hc,hb,hr,hscale,hlife]

end IntegerMultBounds.MathlibTM2.Cost
