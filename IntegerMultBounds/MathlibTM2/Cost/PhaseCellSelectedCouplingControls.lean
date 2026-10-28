module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedMaskCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedNumericalSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRetainedCouplingPass
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInteriorInitialization
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedHalo

/-! Coupling readiness, publication, masks and cleanup have a complete selected bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem couplingPublicationControls_le (P q s t u band a b : ℕ) :
    retainedCouplingControlCost P q s t u band a b+publishHaloCost P q s t u band a b+
      generateRecoveryCouplingMaskCost s t band a b ≤
        (closedPublicationMaskCost s t band a b+closedCouplingSourceMaskCost s t band a b+
          generateRecoveryCouplingMaskCost s t band a b)+prepareCost q (2*q+8)+
          1000*(P+q+s+t+u+band+a+b+1)+1000*s*((2*q+8)+1) := by
  have htop := (Schoenhage.Schedule.topN_facts (by omega : 1 ≤ 2*q+8)).2.1
  dsimp only [retainedCouplingControlCost,publishHaloCost,installCouplingHeadersCost,
    releaseCouplingHeadersCost,publicationSplitCost,publicationSelectFromHeadersCost,publicationMergeCost]
  nlinarith only [htop,Nat.zero_le (s*(2*q+8))]

theorem selectedCouplingPublicationControls_fast_le (cw : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (q u band a b : ℕ),
      2*q+8 ≤ cw*Sizes.p n → u ≤ Sizes.p n → band ≤ Sizes.s n i →
      a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      retainedCouplingControlCost (2^15*Sizes.p n) q (Sizes.s n i) (Sizes.t n i) u band a b+
        publishHaloCost (2^15*Sizes.p n) q (Sizes.s n i) (Sizes.t n i) u band a b+
        generateRecoveryCouplingMaskCost (Sizes.s n i) (Sizes.t n i) band a b ≤
          C*Sizes.t n i*Sizes.p n := by
  let F := 100000000+10000*cw
  obtain ⟨K,hK⟩ := selectedMasks_fast_le
  refine ⟨K+F+1,?_⟩
  filter_upwards [selectedAxis_eventually_polynomial (20020*cw^3) 3] with n hn
  intro h i q u band a b hw hu hband ha hb
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let w := 2*q+8
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hst : s < t := h.good.lt i
  have ht : 1 ≤ t := by omega
  have hpp : p ≤ t*p := Nat.le_mul_of_pos_left _ ht
  have htp : t ≤ t*p := Nat.le_mul_of_pos_right _ hp
  have hq : q ≤ cw*p := by dsimp only [p]; omega
  have hprepare := scalarPrepareCost_arg_le hq hw (by omega)
  have hpoly : prepareCost q w ≤ t := by
    have heq : 20020*(cw*p)^3 = (20020*cw^3)*p^3 := by ring
    exact hprepare.trans (heq.le.trans (hn i))
  have hheaders : 2^15*p+q+s+t+u+band+a+b+1 ≤ (2^15+cw+7)*t*p := by
    have hP := Nat.mul_le_mul_left (2^15) hpp
    have hq' := hq.trans (Nat.mul_le_mul_left cw hpp)
    dsimp only [p,s,t] at *
    nlinarith only [hP,hq',hu,hpp,htp,hst,hband,ha,hb,ht,hp]
  have hwidth : w+1 ≤ (cw+1)*p := by dsimp only [w,p]; nlinarith only [hw,hp]
  have hvolume := Nat.mul_le_mul hst.le hwidth
  have hlinear : 1000*(2^15*p+q+s+t+u+band+a+b+1)+1000*s*(w+1) ≤ F*t*p := by
    dsimp only [F]
    nlinarith only [hheaders,hvolume]
  have hmask := hK n h i band a b hband ha hb
  have hcost := couplingPublicationControls_le (2^15*p) q s t u band a b
  dsimp only [p,s,t,w] at hlinear hpoly hcost ⊢
  nlinarith only [hmask,hcost,hlinear,hpoly,htp]

end IntegerMultBounds.MathlibTM2.Cost
