module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedUniformHaloWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedColumnCouplingWorkspace

/-! Compose the actual uniform Schur residual worker's two shared reserves. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {P₀ U : Type}

theorem selectedInteriorResidualUniformWorkspace_le (J R K rowPush cw : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (_h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
      ∀ u target rhsExp : ℕ,
      let p := Sizes.p m
      let s := Sizes.s m i
      let t := Sizes.t m i
      let l := haloInverseRingLog s t
      executionWidth p l target rhsExp ≤ cw*p → u ≤ p → PhaseCellBand.width p u ≤ s →
      interiorResidualUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J R K rowPush p l s t u target rhsExp ≤ 3*Sizes.T m := by
  filter_upwards [selectedSolveHaloInteriorUniformWorkspace_le J R K cw 1,
    selectedFeedCouplingUniformWorkspace_le (P₀ := P₀) (Q := Q) (A := A) (U := U) false rowPush cw 1,
    selectedAxisPolynomial_le_volume (2000000*(cw+6)) 1 1] with m hh hf hv
  intro h i _ u target rhsExp
  dsimp only
  let p := Sizes.p m
  let s := Sizes.s m i
  let t := Sizes.t m i
  let l := haloInverseRingLog s t
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  intro hw hu hb
  have hhalo := hh h i u target rhsExp hw hu hb
  have hqW : q ≤ w := by dsimp only [q,w,executionPrecision,executionWidth]; omega
  have hwpos : 1 ≤ w := by unfold w executionWidth; omega
  have hfeed := hf h i q w u band hqW hw hwpos hu hb
  simp only [one_mul] at hhalo hfeed
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hbase : p ≤ t*p := Nat.le_mul_of_pos_left _ ht
  have htp : t ≤ t*p := Nat.le_mul_of_pos_right _ hp
  have hunit : 1 ≤ t*p := Nat.mul_pos ht hp
  have hscaled := Nat.mul_le_mul_left (cw+2) hbase
  have hsum : p+q+s+t+u+band+1 ≤ (cw+6)*t*p := by
    have hst : s ≤ t := (h.good.lt i).le
    change band ≤ s at hb
    nlinarith only [hw,hqW,hu,hb,hst,hbase,htp,hunit,hscaled]
  have hscalar := Nat.mul_le_mul_left 2000000 hsum
  have hvolume := hv i
  simp only [pow_one] at hvolume
  have hsmall : 2000000*(p+q+s+t+u+band+1) ≤ Sizes.T m := by
    nlinarith only [hscalar,hvolume]
  unfold interiorResidualUniformWorkspace
  change solveHaloInteriorUniformWorkspace J R K p l s t u target rhsExp+
    feedCouplingUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      false rowPush (2^15*p) q w s t u band+2000000*(p+q+s+t+u+band+1) ≤ 3*Sizes.T m
  nlinarith only [hhalo,hfeed,hsmall]

end IntegerMultBounds.MathlibTM2.Cost
