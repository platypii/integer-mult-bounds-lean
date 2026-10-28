module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInteriorInitialization
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyInteriorFast

/-! Separate all native interior controls from the remaining numerical batch setups. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem cachedHaloClassSharedCost_native_le (p l L s t u target rhsExp a b : ℕ) :
    let P := 2^15*p
    let N := executionStagePrecision p l target rhsExp+1
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let band := PhaseCellBand.width p u
    let V := weightWorkspaceWidth P q w t u
    let H := P+N+q+l+s+t+u+band+a+b+L+1
    cachedHaloClassSharedCost p l L s t u target rhsExp a b ≤
      haloOriginControlsSharedCost P q s t u band a b L+
        advanceControlsSharedCost (haloGeometryWidth t w) s w+
        cachedClosedBatchCost p l 0 L s t u target rhsExp+4000*H*(V+w+1) := by
  dsimp only
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let V := weightWorkspaceWidth P q w t u
  let H := P+N+q+l+s+t+u+band+a+b+L+1
  let R := V+w+1
  have hw : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hs : s ≤ H := by dsimp [H]; omega
  have hwR : w ≤ R := by dsimp [R]; omega
  have hsw := Nat.mul_le_mul hs hwR
  have hHp : H ≤ H*R := Nat.le_mul_of_pos_right _ hR
  have hRp : R ≤ H*R := Nat.le_mul_of_pos_left _ hH
  have hlinear : 10*P+6*N+18*q+6*l+6*s+63*t+25*u+6*band+8*a+8*b+26*L+8*w+21*V+336 ≤
      1000*H+100*R := by dsimp [H,R]; omega
  change cachedHaloClassSharedCost p l L s t u target rhsExp a b ≤
    haloOriginControlsSharedCost P q s t u band a b L+
      advanceControlsSharedCost (haloGeometryWidth t w) s w+
      cachedClosedBatchCost p l 0 L s t u target rhsExp+4000*H*R
  simp only [cachedHaloClassSharedCost,installHaloGroupHeadersCost,installGroupHeadersCost,
    rawNaturalGatherCost,discardBatchOriginsCost,weightWidthCost]
  change _ ≤ _
  dsimp only [P,N,q,w,band,V] at hw hlinear hsw hHp hRp ⊢
  simp only [hw] at *
  nlinarith only [hlinear,hsw,hHp,hRp]

/-- The only remaining shared charges in the interior pass are numerical setup. -/
def familyHaloNumericalSetupCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  ((haloLengthCandidates s t (PhaseCellBand.width p u) a b).map
    (fun L => cachedClosedBatchCost p l 0 L s t u target rhsExp)).sum

theorem familyHaloControlCost_native_fast_le (cw cl : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)) (l u target rhsExp a b : ℕ),
      executionWidth (Sizes.p n) l target rhsExp ≤ cw*Sizes.p n → l ≤ cl*Sizes.p n →
      u ≤ Sizes.p n → PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      familyHaloControlCost (Sizes.p n) l (Sizes.s n i) (Sizes.t n i) u target rhsExp a b ≤
        familyHaloNumericalSetupCost (Sizes.p n) l (Sizes.s n i) (Sizes.t n i) u target rhsExp a b+
          C*Sizes.t n i*Sizes.p n := by
  let cV := 2*cw+426009
  let cH := 2^15+2*cw+cl+8
  let cR := cV+cw+1
  let K := 4000*cH*cR
  let J := 4096*(16*(Nat.size cw+13)^2+cV+1)
  obtain ⟨Cinit,hinit⟩ := selectedExecutionLengthKeyInitialization_fast_le cw cl
  obtain ⟨Cshared,hshared⟩ := selectedSharedHaloControlCandidates_fast_le cw
  refine ⟨Cinit+Cshared+6*K+J+2*(cV+cw)+207,?_⟩
  intro n h i l u target rhsExp a b hw hl hu hband ha hb
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let V := weightWorkspaceWidth P q w t u
  let lengths := haloLengthCandidates s t band a b
  have hp := h.thirteen_le_p
  have hpt := selectedPrecision_le_axis h i
  have hst := h.good.lt i
  have ht : 1 ≤ t := by dsimp [t]; omega
  have htp : 1 ≤ t*p := by dsimp [p,t]; nlinarith
  have hq : q ≤ cw*p := by
    have hh : q ≤ w := by dsimp [q,w,executionPrecision,executionWidth]; omega
    exact hh.trans hw
  have hN : N ≤ cw*p := by
    have hh : N ≤ w := by dsimp [N,w,executionStagePrecision,executionWidth]; omega
    exact hh.trans hw
  have hqw : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  have hV := selectedWeightWorkspaceWidth_le cw h i q w u hw (by dsimp [q,w,executionPrecision,executionWidth]; omega) hu
  change V ≤ cV*p at hV
  have hR : V+w+1 ≤ cR*p := by dsimp only [cR]; dsimp only [p] at *; nlinarith only [hV,hw,hp]
  have hclass : ∀ L ∈ lengths,
      cachedHaloClassSharedCost p l L s t u target rhsExp a b ≤
        (haloOriginControlsSharedCost P q s t u band a b L+
          advanceControlsSharedCost (haloGeometryWidth t w) s w)+
          cachedClosedBatchCost p l 0 L s t u target rhsExp+K*t*p := by
    intro L hL
    have hlen := haloLengthCandidates_uniform hst band a b hL
    have hdiv := Nat.div_le_self s (t-s)
    have hLt : L ≤ t := by dsimp only [s,t] at *; omega
    have hH : P+N+q+l+s+t+u+band+a+b+L+1 ≤ cH*t := by
      have hP := Nat.mul_le_mul_left (2^15) hpt
      have hq' := hq.trans (Nat.mul_le_mul_left cw hpt)
      have hN' := hN.trans (Nat.mul_le_mul_left cw hpt)
      have hl' := hl.trans (Nat.mul_le_mul_left cl hpt)
      dsimp only [P,cH,p,s,t,band] at *
      nlinarith only [hP,hq',hN',hl',hu,hpt,hst,hband,ha,hb,hLt,ht]
    have hprod := Nat.mul_le_mul hH hR
    have hc := cachedHaloClassSharedCost_native_le p l L s t u target rhsExp a b
    change _ ≤ _+4000*(P+N+q+l+s+t+u+band+a+b+L+1)*(V+w+1) at hc
    dsimp only [K]
    nlinarith only [hc,hprod]
  have hsum := List.sum_le_sum (f := fun L => cachedHaloClassSharedCost p l L s t u target rhsExp a b)
    (g := fun L => (haloOriginControlsSharedCost P q s t u band a b L+
      advanceControlsSharedCost (haloGeometryWidth t w) s w)+
      cachedClosedBatchCost p l 0 L s t u target rhsExp+K*t*p) hclass
  have hcontrols := hshared n h i q u band a b hq hu hband ha hb
  simp only [hqw,List.sum_map_add,List.map_const',List.sum_replicate,nsmul_eq_mul] at hcontrols
  have hsetup := hinit n h i l u target rhsExp a b hw hl hu hband ha hb
  have hcells := selectedHaloControlCells_le cw cV h i P q w u hw hV
  have htail : 2*(V+w)+207 ≤ (2*(cV+cw)+207)*t*p := by
    have hpp : p ≤ t*p := Nat.le_mul_of_pos_left _ ht
    nlinarith only [hV,hw,htp,hpp]
  simp only [List.sum_map_add,List.map_const',List.sum_replicate,nsmul_eq_mul] at hsum
  have hlength : lengths.length = 6 := by simp [lengths,haloLengthCandidates,naturalLengthCandidates]
  change _+lengths.length * _ ≤ _ at hcontrols
  rw [hlength] at hsum hcontrols
  change _ ≤ familyHaloNumericalSetupCost p l s t u target rhsExp a b+_
  dsimp only [familyHaloControlCost,familyHaloNumericalSetupCost]
  dsimp only [lengths,P,N,q,w,band,V,J,p,s,t] at hsum hcontrols hsetup hcells htail ⊢
  nlinarith only [hsum,hcontrols,hsetup,hcells,htail]

theorem selectedInteriorNativeControls_fast_le (ct : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
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
          familyHaloNumericalSetupCost p l s t u firstTarget 2 a b+
            familyHaloNumericalSetupCost p l s t u secondTarget recoveryExp a b+C*t*p := by
  obtain ⟨C,hC⟩ := familyHaloControlCost_native_fast_le (1032+8*ct) 20
  refine ⟨2*C,?_⟩
  intro n h i _ u target a b hu htarget hband ha hb
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
  have hl := (haloInverseRingLog_bounds hp hst hθ).1
  have hfirst := hC n h i l u firstTarget 2 a b hw hl hu hband ha hb
  have hE : executionExponent p l firstTarget 2 = executionExponent p l secondTarget recoveryExp :=
    recovery_execution_exponent p l secondTarget 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
  have hw₂ : executionWidth p l secondTarget recoveryExp ≤ (1032+8*ct)*p := by
    simpa only [executionWidth,← hE] using hw
  have hsecond := hC n h i l u secondTarget recoveryExp a b hw₂ hl hu hband ha hb
  dsimp only [p,s,t,l,firstTarget,secondTarget,recoveryExp,bits] at hfirst hsecond ⊢
  nlinarith only [hfirst,hsecond]

end IntegerMultBounds.MathlibTM2.Cost
