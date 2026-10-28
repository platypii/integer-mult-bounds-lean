module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedNumericalSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellInteriorControlRemainder

/-! Close the actual six-candidate numerical setup sum and the interior control ledger. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedCachedZeroBatch_fast_le (cw cl cr cL : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (l u target rhsExp L : ℕ),
      executionWidth (Sizes.p n) l target rhsExp ≤ cw*Sizes.p n → l ≤ cl*Sizes.p n →
      2^l ≤ cr*Sizes.p n → u ≤ Sizes.p n → PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      L ≤ cL*Sizes.p n →
      cachedClosedBatchCost (Sizes.p n) l 0 L (Sizes.s n i) (Sizes.t n i) u target rhsExp ≤ C*Sizes.t n i := by
  let cW := 2^15*(cw+2)+cw+5
  let cZ := cW+cw+cl+cL+cr+2
  let K := (8*mtCvKf 10+1000000)*cZ^3
  obtain ⟨C,hheader⟩ := selectedHeaderGeneratorSetup_fast_le (2^15) cw cw cL
  refine ⟨C+1,?_⟩
  filter_upwards [hheader,selectedAxis_eventually_polynomial K 6] with n hh hn
  intro h i l u target rhsExp L hw hl hr hu hband hL
  let p := Sizes.p n
  let q := executionPrecision p l target rhsExp
  let N := executionStagePrecision p l target rhsExp+1
  let Z := cZ*p^2
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hsq : p ≤ p^2 := by nlinarith only [hp]
  have hq : q ≤ cw*p := by
    have hh : q ≤ executionWidth p l target rhsExp := by dsimp [q,executionPrecision,executionWidth]; omega
    exact hh.trans hw
  have hN : N ≤ cw*p := by
    have hh : N ≤ executionWidth p l target rhsExp := by dsimp [N,executionStagePrecision,executionWidth]; omega
    exact hh.trans hw
  have hhead := hh h i (2^15*p) N q u (PhaseCellBand.width p u) L le_rfl hN hq hu hband hL
  obtain ⟨hwidth,_⟩ := selectedConstructionWidths_le (2^15) cw cw cL h i le_rfl hN hq hu hband hL
  have hparam (x c : ℕ) (hx : x ≤ c*p) (hc : c ≤ cZ) : x ≤ Z :=
    hx.trans ((Nat.mul_le_mul_left c hsq).trans (Nat.mul_le_mul_right (p^2) hc))
  have hzcoef : 1 ≤ cZ := by dsimp only [cZ]; omega
  have hZ : 1 ≤ Z := by
    dsimp only [Z]
    simpa only [Nat.one_mul] using Nat.mul_le_mul hzcoef (Nat.one_le_pow 2 p hp)
  have hpZ := hparam p 1 (by simp) hzcoef
  have hlZ := hparam l cl hl (by dsimp only [cZ]; omega)
  have hLZ := hparam L cL hL (by dsimp only [cZ]; omega)
  have hrZ := hparam (2^l) cr hr (by dsimp only [cZ]; omega)
  have hwZ := hparam (executionWidth p l target rhsExp) cw hw (by dsimp only [cZ]; omega)
  have hWZ : integerSetupWidth (2^15*p) q (N+1) 0 ≤ Z :=
    hwidth.trans (Nat.mul_le_mul_right (p^2) (by dsimp only [cZ]; omega : cW ≤ cZ))
  have hc := cachedClosedBatchCost_zero_poly (s := Sizes.s n i) (t := Sizes.t n i) (u := u)
    hZ hpZ hlZ hLZ hrZ hwZ hWZ
  have hpoly : (8*mtCvKf 10+1000000)*Z^3 ≤ Sizes.t n i := by
    have heq : (8*mtCvKf 10+1000000)*Z^3 = K*p^6 := by
      dsimp only [Z,K]
      rw [mul_pow,← pow_mul]
      ring
    rw [heq]
    exact hn i
  change _ ≤ headerGeneratorSetupCost (2^15*p) N q (Sizes.s n i) (Sizes.t n i) u
    (PhaseCellBand.width p u) L+_ at hc
  exact hc.trans ((Nat.add_le_add hhead hpoly).trans_eq (by ring))

theorem selectedNumericalSetupSum_fast_le (cw cl cr : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ l u target rhsExp a b : ℕ,
      executionWidth (Sizes.p n) l target rhsExp ≤ cw*Sizes.p n → l ≤ cl*Sizes.p n →
      2^l ≤ cr*Sizes.p n → u ≤ Sizes.p n → PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      familyHaloNumericalSetupCost (Sizes.p n) l (Sizes.s n i) (Sizes.t n i) u target rhsExp a b ≤
        C*Sizes.t n i := by
  obtain ⟨C,hC⟩ := selectedCachedZeroBatch_fast_le cw cl cr 5
  refine ⟨6*C,?_⟩
  filter_upwards [hC] with n hn
  intro h i _ l u target rhsExp a b hw hl hr hu hband
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hcell := phaseGap_cellLength_le hp (h.good.lt i) (h.quarter_p_le_theta i)
  have hcost : ∀ L ∈ haloLengthCandidates (Sizes.s n i) (Sizes.t n i) (PhaseCellBand.width (Sizes.p n) u) a b,
      cachedClosedBatchCost (Sizes.p n) l 0 L (Sizes.s n i) (Sizes.t n i) u target rhsExp ≤ C*Sizes.t n i := by
    intro L hL
    have hlen := haloLengthCandidates_uniform (h.good.lt i) (PhaseCellBand.width (Sizes.p n) u) a b hL
    exact hn h i l u target rhsExp L hw hl hr hu hband (by omega)
  have hsum := List.sum_le_length_nsmul
    ((haloLengthCandidates (Sizes.s n i) (Sizes.t n i) (PhaseCellBand.width (Sizes.p n) u) a b).map
      (fun L => cachedClosedBatchCost (Sizes.p n) l 0 L (Sizes.s n i) (Sizes.t n i) u target rhsExp))
      (C*Sizes.t n i) (by
        intro x hx
        obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hx
        exact hcost L hL)
  have hlength : (haloLengthCandidates (Sizes.s n i) (Sizes.t n i)
      (PhaseCellBand.width (Sizes.p n) u) a b).length = 6 := by
    simp [haloLengthCandidates,naturalLengthCandidates]
  simpa only [familyHaloNumericalSetupCost,List.length_map,hlength,nsmul_eq_mul,Nat.cast_ofNat,Nat.mul_assoc] using hsum

theorem familyHaloControlCost_selected_fast_le (cw cl cr : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ l u target rhsExp a b : ℕ,
      executionWidth (Sizes.p n) l target rhsExp ≤ cw*Sizes.p n → l ≤ cl*Sizes.p n →
      2^l ≤ cr*Sizes.p n → u ≤ Sizes.p n → PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      familyHaloControlCost (Sizes.p n) l (Sizes.s n i) (Sizes.t n i) u target rhsExp a b ≤
        C*Sizes.t n i*Sizes.p n := by
  obtain ⟨C,hC⟩ := familyHaloControlCost_native_fast_le cw cl
  obtain ⟨K,hK⟩ := selectedNumericalSetupSum_fast_le cw cl cr
  refine ⟨C+K,?_⟩
  filter_upwards [hK] with n hn
  intro h i _ l u target rhsExp a b hw hl hr hu hband ha hb
  have hc := hC n h i l u target rhsExp a b hw hl hu hband ha hb
  have hk := hn h i l u target rhsExp a b hw hl hr hu hband
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hscaled := Nat.mul_le_mul_left (K*Sizes.t n i) hp
  nlinarith only [hc,hk,hscaled]

theorem selectedInteriorControls_fast_le (ct : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (u target a b : ℕ), u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
        (haloBoundary s t (PhaseCellBand.width p u) a b).card
      let firstTarget := initialSchurTarget p u bits 2
      let secondTarget := recoveryTarget p bits
      let recoveryExp := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
      familyHaloControlCost p l s t u firstTarget 2 a b+
        familyHaloControlCost p l s t u secondTarget recoveryExp a b ≤
          C*t*p := by
  obtain ⟨C,hC⟩ := familyHaloControlCost_selected_fast_le (1032+8*ct) 20 20
  refine ⟨2*C,?_⟩
  filter_upwards [hC] with n hn
  intro h i _ u target a b hu htarget hband ha hb
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
    (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let firstTarget := initialSchurTarget p u bits 2
  let secondTarget := recoveryTarget p bits
  let recoveryExp := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
  have hw := selectedInverseWorkingWidth_le ct h i u target a b htarget hband
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp [p]; omega
  have hst : s < t := h.good.lt i
  have hθ := h.quarter_p_le_theta i
  obtain ⟨hl,hr⟩ := haloInverseRingLog_bounds hp hst hθ
  have hfirst := hn h i l u firstTarget 2 a b hw hl hr hu hband ha hb
  have hE : executionExponent p l firstTarget 2 = executionExponent p l secondTarget recoveryExp :=
    recovery_execution_exponent p l secondTarget 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
  have hw₂ : executionWidth p l secondTarget recoveryExp ≤ (1032+8*ct)*p := by
    simpa only [executionWidth,← hE] using hw
  have hsecond := hn h i l u secondTarget recoveryExp a b hw₂ hl hr hu hband ha hb
  dsimp only [p,s,t,l,firstTarget,secondTarget,recoveryExp,bits] at hfirst hsecond ⊢
  nlinarith only [hfirst,hsecond]

end IntegerMultBounds.MathlibTM2.Cost
