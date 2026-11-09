module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellUncachedInteriorPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInteriorFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSchurColumn
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFamilyBatchFast

/-! Weight construction is uniform in the derivation of the working target. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedInteriorConstruction_width_weights_le (c : ℕ) :
    ∃ K : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b : ℕ, u ≤ Sizes.p n →
      executionWidth (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target 2 ≤ c*Sizes.p n →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      solveHaloInteriorCost p l s t u target 2 a b ≤
        familyHaloInteriorGeometryCost p l s t u target 2 a b+K*t*p^4 := by
  let cZ := 3*c+500000
  refine ⟨10000000*cZ^4,?_⟩
  intro n h i _ u target a b hu hwidth
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let band := PhaseCellBand.width p u
  let stage := target
  let q := executionPrecision p l stage 2
  let w := executionWidth p l stage 2
  let Z := cZ*p
  have hw : w ≤ c*p := hwidth
  have hq : q ≤ c*p := (show q ≤ w by dsimp [q,w,executionPrecision,executionWidth]; omega).trans hw
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hst : s < t := h.good.lt i
  have hZ : 1 ≤ Z := by dsimp only [Z,cZ]; nlinarith only [hp]
  have hparam (x d : ℕ) (hx : x ≤ d*p) (hd : d ≤ cZ) : x ≤ Z :=
    hx.trans (Nat.mul_le_mul_right p hd)
  have hPZ := hparam (2^15*p) (2^15) le_rfl (by dsimp only [cZ]; omega)
  have hwZ := hparam w c hw (by dsimp only [cZ]; omega)
  have hqZ := hparam q c hq (by dsimp only [cZ]; omega)
  have hNZ : executionStagePrecision p l stage 2+1 ≤ Z :=
    (show executionStagePrecision p l stage 2+1 ≤ w by dsimp only [w,executionWidth,executionStagePrecision]; omega).trans hwZ
  obtain ⟨hl,_⟩ := haloInverseRingLog_bounds hp hst (h.quarter_p_le_theta i)
  have hlZ := hparam l 20 hl (by dsimp only [cZ]; omega)
  have huZ := hparam u 1 (by simpa using hu) (by dsimp only [cZ]; omega)
  have hv := selectedWeightWorkspaceWidth_le c h i q w u hw
    (by dsimp only [q,w,executionPrecision,executionWidth]; omega) hu
  have hvZ := hparam _ (2*c+426009) hv (by dsimp only [cZ]; omega)
  have hcell := phaseGap_cellLength_le hp hst (h.quarter_p_le_theta i)
  have hkeys : ∀ L ∈ haloLengthCandidates s t band a b, L ≤ Z := by
    intro L hL
    have hlen := haloLengthCandidates_uniform hst band a b hL
    apply hparam L 5 (by omega)
    dsimp only [cZ]; omega
  have hcost := haloInteriorCostBound_weights_poly p l u stage 2 a b Z hst hZ
    hPZ hNZ hqZ hlZ huZ hwZ hvZ hkeys
  have hrun := solveHaloInteriorCost_le hst p l u stage 2 a b
  have heq : 10000000*t*Z^4 = (10000000*cZ^4)*t*p^4 := by dsimp only [Z]; ring
  rw [heq] at hcost
  exact hrun.trans hcost

end IntegerMultBounds.MathlibTM2.Cost
