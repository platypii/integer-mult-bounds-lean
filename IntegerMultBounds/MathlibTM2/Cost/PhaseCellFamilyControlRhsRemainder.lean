module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyCouplingFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCouplingControls
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedSetup

/-! Isolate boundary RHS gathering from the otherwise linear selected caller controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem familyComplexControlRemainingCost_rhs_le (p u l s t a b target : ℕ) [NeZero s] :
    let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
    let j := initialSchurTarget p u bits 2
    let k := recoveryTarget p bits
    let e := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
    let q := executionPrecision p l j 2
    let w := executionWidth p l j 2
    familyComplexControlRemainingCost p u l s t a b target ≤
      2*boundaryRhsPrepareCost (publicationGeometryWidth t (PhaseCellBand.width p u)) w N s+
      2*(familyHaloControlCost p l s t u j 2 a b+familyHaloControlCost p l s t u k e a b)+
      4*retainedCouplingControlCost (2^15*p) q s t u (PhaseCellBand.width p u) a b+
      2*publishHaloCost (2^15*p) q s t u (PhaseCellBand.width p u) a b+
      10000*(s+1)*(w+1) := by
  dsimp only
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let j := initialSchurTarget p u bits 2
  let k := recoveryTarget p bits
  let e := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
  let q := executionPrecision p l j 2
  let w := executionWidth p l j 2
  have hN : N ≤ s := by simpa [N] using Finset.card_le_univ (s := haloBoundary s t (PhaseCellBand.width p u) a b)
  have hE : executionExponent p l j 2 = executionExponent p l k e :=
    recovery_execution_exponent p l k 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
  have hq : executionPrecision p l k e = q := by simp only [q,executionPrecision,← hE]
  have hqw : 2*q+8 = w := by dsimp only [q,w,executionPrecision,executionWidth]; omega
  have hqw' : q ≤ w := by omega
  have hambient := sharedPageBoundaryAmbientCost_le N w s hN
  have hretire : retireCountedLineCost N w ≤ retireCountedLineCost s w := by
    unfold retireCountedLineCost
    gcongr
  have hc := familyComplexNonBoundaryRemainingCost_coupling_split p u l s t a b target
  have hb := familyComplexRemainingLineCost_boundary_split p u l s t a b target
  have heq : familyComplexControlRemainingCost p u l s t a b target+
      4*familyCouplingLineCost p u l s t a b target+2*familyBoundaryLineCost p u l s t a b target =
      familyComplexRemainingLineCost p u l s t a b target+
        4*familyCouplingLineControlCost p u l s t a b target := by
    dsimp only [familyComplexControlRemainingCost]
    omega
  dsimp only [familyComplexRemainingLineCost,familyRealComponentRemainingCost,
    familyRealResidualRemainingCost,familyRecoveryRemainingCost,familyCouplingLineCost,
    familyCouplingLineControlCost,familyBoundaryLineCost] at heq
  dsimp only [N,bits,j,k,e,q,w,initialSchurTarget] at hq hqw hqw' hambient hretire heq ⊢
  rw [hq] at heq
  simp only [← hqw] at heq hambient hretire hqw' ⊢
  dsimp only [originalComponentInputsCost,saveOriginalInputCost,preparedComponentInputsCost,
    retainedComponentInputsCost,cleanComponentTransitionCost,cleanFinishComponentsCost,
    initializeInteriorOutputCost,realResidualProjectionCost,retireAmbientSourceCost,
    sharedPageRetireResidualCost,retireCountedLineCost] at heq hretire
  nlinarith only [heq,hambient,hretire,hqw']

theorem selectedFamilyControls_rhs_fast_le (ct : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let w := executionWidth p l (initialSchurTarget p u bits 2) 2
      familyComplexControlRemainingCost p u l s t a b target ≤
        2*boundaryRhsPrepareCost (publicationGeometryWidth t (PhaseCellBand.width p u)) w N s+C*t*p := by
  let cw := 1032+8*ct
  obtain ⟨C,hC⟩ := selectedInteriorControls_fast_le ct
  obtain ⟨K,hK⟩ := selectedCouplingPublicationControls_fast_le cw
  refine ⟨2*C+4*K+10000*(cw+1),?_⟩
  filter_upwards [hC,hK] with n hn hk
  intro h i _ u target a b hu htarget hband ha hb
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let j := initialSchurTarget p u bits 2
  let k := recoveryTarget p bits
  let e := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
  let q := executionPrecision p l j 2
  let w := executionWidth p l j 2
  have hw := selectedInverseWorkingWidth_le ct h i u target a b htarget hband
  have hqw : 2*q+8 = w := by dsimp only [q,w,executionPrecision,executionWidth]; omega
  have hwidth : 2*q+8 ≤ cw*p := by rw [hqw]; exact hw
  have hc := hn h i u target a b hu htarget hband ha hb
  change familyHaloControlCost p l s t u j 2 a b+familyHaloControlCost p l s t u k e a b ≤ C*t*p at hc
  have hcp := hk h i q u (PhaseCellBand.width p u) a b hwidth hu hband ha hb
  have hcp4 := Nat.mul_le_mul_left 4 hcp
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hst : s+1 ≤ t := h.good.lt i
  have hw' : w+1 ≤ (cw+1)*p := by nlinarith only [hwidth,hqw,hp]
  have hvolume := Nat.mul_le_mul hst hw'
  have htail : 10000*(s+1)*(w+1) ≤ 10000*(cw+1)*t*p := by nlinarith only [hvolume]
  have hcost := familyComplexControlRemainingCost_rhs_le p u l s t a b target
  change familyComplexControlRemainingCost p u l s t a b target ≤
    2*boundaryRhsPrepareCost (publicationGeometryWidth t (PhaseCellBand.width p u)) w N s+
      2*(familyHaloControlCost p l s t u j 2 a b+familyHaloControlCost p l s t u k e a b)+
      4*retainedCouplingControlCost (2^15*p) q s t u (PhaseCellBand.width p u) a b+
      2*publishHaloCost (2^15*p) q s t u (PhaseCellBand.width p u) a b+
      10000*(s+1)*(w+1) at hcost
  dsimp only [p,s,t] at hc hcp4 htail hcost ⊢
  nlinarith only [hc,hcp4,htail,hcost,
    Nat.zero_le (publishHaloCost (2^15*Sizes.p n) q (Sizes.s n i) (Sizes.t n i) u
      (PhaseCellBand.width (Sizes.p n) u) a b),
    Nat.zero_le (generateRecoveryCouplingMaskCost (Sizes.s n i) (Sizes.t n i)
      (PhaseCellBand.width (Sizes.p n) u) a b)]

end IntegerMultBounds.MathlibTM2.Cost
