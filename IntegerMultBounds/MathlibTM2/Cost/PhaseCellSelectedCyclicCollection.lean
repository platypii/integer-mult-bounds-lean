module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicCollectionCostBound
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedBoundaryWidths
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicWorkingWidth

/-! Selected collection and retirement are uniformly cubic in axis length. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedCyclicColumnControls_poly_le (cq cV : ℕ) {n : ℕ}
    (h : Sizes.Big n) (i : Fin (Sizes.d n)) (q V band k j : ℕ)
    (hq : q ≤ cq*Sizes.p n) (hV : V ≤ cV*Sizes.p n)
    (hb : band ≤ Sizes.s n i) (hk : k ≤ Sizes.s n i) (hj : j ≤ Sizes.s n i) :
    10000*(k+j+band+V+1)*(q+V+1) ≤
      (10000*(cV+4)*(cq+cV+1))*(Sizes.t n i)^2 := by
  have hp := selectedPrecision_le_axis h i
  have hs := (h.good.lt i).le
  have ht : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have hq' := hq.trans (Nat.mul_le_mul_left cq hp)
  have hV' := hV.trans (Nat.mul_le_mul_left cV hp)
  have hl : k+j+band+V+1 ≤ (cV+4)*Sizes.t n i := by
    nlinarith only [hs,hb,hk,hj,hV',ht]
  have hr : q+V+1 ≤ (cq+cV+1)*Sizes.t n i := by
    nlinarith only [hq',hV',ht]
  have hm := Nat.mul_le_mul hl hr
  nlinarith only [hm]

theorem selectedCollectRetireCyclicColumnCost_poly_le (cq cV : ℕ) {n : ℕ}
    (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
    (B : Finset (ZMod (Sizes.s n i))) (q V band a b k : ℕ)
    (hq : q ≤ cq*Sizes.p n) (hV : V ≤ cV*Sizes.p n)
    (hband : band ≤ Sizes.s n i) (ha : a ≤ Sizes.s n i) (hb : b ≤ Sizes.s n i)
    (hk : k ≤ B.card) :
    collectRetireCyclicColumnCost B q V band a b k ≤
      (6010000*(cq+cV+1)^3)*(Sizes.t n i)^3 := by
  let Z := (cq+cV+1)*Sizes.t n i
  have hp := selectedPrecision_le_axis h i
  have hs := (h.good.lt i).le
  have ht : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have htZ : Sizes.t n i ≤ Z := by dsimp [Z]; nlinarith only [Nat.zero_le ((cq+cV)*Sizes.t n i)]
  have hqZ : q ≤ Z := by
    have hq' := hq.trans (Nat.mul_le_mul_left cq hp)
    dsimp [Z]; nlinarith only [hq',Nat.zero_le (cV*Sizes.t n i)]
  have hVZ : V ≤ Z := by
    have hV' := hV.trans (Nat.mul_le_mul_left cV hp)
    dsimp [Z]; nlinarith only [hV',Nat.zero_le (cq*Sizes.t n i)]
  have hrows : B.card ≤ Sizes.s n i := by simpa only [ZMod.card] using B.card_le_univ
  have hc := collectRetireCyclicColumnCost_poly B q V band a b k Z ha hb hk
    (ht.trans htZ) hqZ hVZ (hs.trans htZ) (hrows.trans (hs.trans htZ))
    (hband.trans (hs.trans htZ))
  simpa only [Z,mul_pow,Nat.mul_assoc] using hc

theorem selectedJointCyclicCollection_poly_le (ct : ℕ) :
    ∃ C : ℕ, ∀ n (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a span x y k : ℕ, target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → x ≤ Sizes.s n i → y ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let band := PhaseCellBand.width p u
      let B := cyclicPrincipalBoundary s t band a span
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
      let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
      k ≤ B.card → collectRetireCyclicColumnCost B q (publicationGeometryWidth t band) band x y k ≤ C*t^3 := by
  obtain ⟨c,hc,hwidths⟩ := selectedInverseBoundaryWidths_le ct
  refine ⟨6010000*((1032+8*ct)+c+1)^3,?_⟩
  intro n h i _ u target a span x y k htarget hband hx hy
  dsimp only
  intro hk
  have hw := selectedCyclicWorkingWidth_le ct h i u target a span htarget hband
  have hqw (p l target rhsExp : ℕ) : executionPrecision p l target rhsExp ≤ executionWidth p l target rhsExp := by
    unfold executionPrecision executionWidth
    omega
  have hq := (hqw _ _ _ _).trans hw
  obtain ⟨_,_,_,_,hV,_,_⟩ := hwidths n h i u target 0 0 htarget hband
  exact selectedCollectRetireCyclicColumnCost_poly_le (1032+8*ct) c h i _ _ _ _ x y k
    hq hV hband hx hy hk

end IntegerMultBounds.MathlibTM2.Cost
