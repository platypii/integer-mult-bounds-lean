module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedKeyCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedRetainedCouplingCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecovery

/-! Recovery uses the same keyed arithmetic geometry as the initial pass.
Its input conversion and retained coupling work are priced separately. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem packedBoundaryRecoveryInputsCost_poly {V N n w t Z : ℕ}
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hV : V ≤ Z) (hN : N ≤ t) (hn : n ≤ t) (hw : w ≤ Z) :
    packedBoundaryRecoveryInputsCost V N n w ≤ 10000*t*Z^2 := by
  have hmono : packedBoundaryRecoveryInputsCost V N n w ≤ packedBoundaryRecoveryInputsCost Z t t Z := by
    unfold packedBoundaryRecoveryInputsCost packedBoundaryRecoveryFieldCost packedRecoveryRhsInputCost
      moveCountedLineCost generatedBoundaryUnfoldCost packedRecoveryDestinationCost retireCountedLineCost copyCountedLineCost
    gcongr
  apply hmono.trans
  unfold packedBoundaryRecoveryInputsCost packedBoundaryRecoveryFieldCost packedRecoveryRhsInputCost
    moveCountedLineCost generatedBoundaryUnfoldCost packedRecoveryDestinationCost retireCountedLineCost copyCountedLineCost
  have htZ := Nat.mul_le_mul_left t hZ
  have hZt := Nat.mul_le_mul_left Z ht
  have hpow : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  have hscale := Nat.mul_le_mul_left t hpow
  nlinarith only [htZ,hZt,hscale,hZ,ht]

theorem packedBoundaryRecoveryCost_geometry_le {s t : ℕ} [NeZero s] (hst : s < t)
    (p u l target rhsExp a b V q w Z : ℕ) (hb : b ≤ s) (hZ : 1 ≤ Z) (hw : w ≤ Z) (hV : V ≤ Z) :
    let band := PhaseCellBand.width p u
    let n := (haloBoundary s t band a b).card
    let k := boundaryHaloRecoveryTarget p (boundaryRecoveryTarget p target) n
    let e := recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)
    (∀ L ∈ haloLengthKeys s t band a b, ∀ x ∈ packedHaloKeyDimensions p l s t u k e a b V L, x ≤ Z) →
    packedBoundaryRecoveryCost p u l target rhsExp s t a b V q w ≤
      haloInteriorCostBound p l s t u k e a b+
        preparedSharedLocalFeedCouplingIntervalCost true (2^15*p) q w s t u band a b a (b-a) V+
        1000000*t*Z^4 := by
  dsimp only
  intro hd
  let n := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let k := boundaryHaloRecoveryTarget p (boundaryRecoveryTarget p target) n
  let e := recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)
  have hloop := packedHaloKeyLoopCost_geometry_le hst p l u k e a b V Z hZ hd
  have hinit := initializeHaloLengthKeysCost_le (2^15*p) (executionStagePrecision p l k e+1)
    (executionPrecision p l k e) l s t u (PhaseCellBand.width p u) a b
  have hsum := List.sum_le_sum (l := haloLengthCandidates s t (PhaseCellBand.width p u) a b)
    (fun L _ => show sizedClosedBatchBound p l 0 L s t u k e ≤ haloClassSharedCost p l L s t u k e a b by
      dsimp only [haloClassSharedCost]
      omega)
  have hcell := Nat.mul_le_mul_left (t-s+1)
    (show batchCellCost p l t u k e ≤ haloClassCellCost p l t u k e by dsimp only [haloClassCellCost]; omega)
  have ht : 1 ≤ t := by have := NeZero.pos s; omega
  have hN : b-a ≤ t := (Nat.sub_le b a).trans (hb.trans hst.le)
  have hn : n ≤ t := (show n ≤ s by simpa only [n,ZMod.card] using (haloBoundary s t (PhaseCellBand.width p u) a b).card_le_univ).trans hst.le
  have hinput := packedBoundaryRecoveryInputsCost_poly ht hZ hV hN hn hw
  have hdiv : (s/(t-s)+1)-2*PhaseCellBand.width p u ≤ t+1 := by have := Nat.div_le_self s (t-s); omega
  have hcontrols : 1+(2*(2*V+((s/(t-s)+1)-2*PhaseCellBand.width p u)+w)+9) ≤ 1000*t*Z^2 := by
    have htZ := Nat.mul_le_mul_left t hZ
    have hZt := Nat.mul_le_mul_left Z ht
    have hpow : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
    have hscale := Nat.mul_le_mul_left t hpow
    nlinarith only [htZ,hZt,hscale,hV,hw,hdiv,hZ,ht]
  have hpow : Z^2 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have hscale := Nat.mul_le_mul_left t hpow
  have hcontrolScale : Z^4 ≤ t*Z^4 := Nat.le_mul_of_pos_left _ ht
  have hunit : 1 ≤ t*Z^4 := Nat.mul_pos ht (one_le_pow₀ hZ)
  dsimp only [packedBoundaryRecoveryCost,haloInteriorCostBound]
  dsimp only [k,e,n] at hloop hinit hsum hcell hinput
  nlinarith only [hloop,hinit,hsum,hcell,hinput,hcontrols,hscale,hcontrolScale,hunit]

/-- The recovery pass inherits the scalar estimate at its own precision.
Retained coupling and tape conversion contribute only a polynomial allowance. -/
theorem packedBoundaryRecoveryCost_weights_poly {s t : ℕ} [NeZero s] (hst : s < t)
    (p u l target rhsExp a b V q w Z : ℕ) (hb : b ≤ s) (hZ : 1 ≤ Z)
    (hP : 2^15*p ≤ Z) (hl : l ≤ Z) (hu : u ≤ Z)
    (hq : q ≤ Z) (hw : w ≤ Z) (hpos : 1 ≤ w) (hband : PhaseCellBand.width p u ≤ Z) (hV : V ≤ Z) :
    let band := PhaseCellBand.width p u
    let n := (haloBoundary s t band a b).card
    let k := boundaryHaloRecoveryTarget p (boundaryRecoveryTarget p target) n
    let e := recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)
    executionStagePrecision p l k e+1 ≤ Z → executionPrecision p l k e ≤ Z → executionWidth p l k e ≤ Z →
    weightWorkspaceWidth (2^15*p) (executionPrecision p l k e) (executionWidth p l k e) t u ≤ Z →
    (∀ L ∈ haloLengthCandidates s t band a b, L ≤ Z) →
    (∀ L ∈ haloLengthKeys s t band a b, ∀ x ∈ packedHaloKeyDimensions p l s t u k e a b V L, x ≤ Z) →
    packedBoundaryRecoveryCost p u l target rhsExp s t a b V q w ≤
      familyHaloInteriorGeometryCost p l s t u k e a b+13000000*(ssMulConst+1)*t*Z^4 := by
  dsimp only
  intro hstage hqRec hwRec hVRec hkeys hd
  let n := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let k := boundaryHaloRecoveryTarget p (boundaryRecoveryTarget p target) n
  let e := recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)
  have hgeometry := packedBoundaryRecoveryCost_geometry_le hst p u l target rhsExp a b V q w Z hb hZ hw hV hd
  have hscalar := haloInteriorCostBound_weights_poly p l u k e a b Z hst hZ hP hstage hqRec hl hu hwRec hVRec hkeys
  have ht : 1 ≤ t := by have := NeZero.pos s; omega
  have hN : b-a ≤ t := (Nat.sub_le b a).trans (hb.trans hst.le)
  have hcoupling := preparedSharedLocalFeedCouplingIntervalCost_poly
    (P := 2^15*p) (s := s) (u := u) (a := a) (b := b) (origin := a)
    ht hZ hN hq hw hpos hband hV true
  have hS : 1 ≤ ssMulConst+1 := by omega
  have hscale : t*Z^4 ≤ (ssMulConst+1)*t*Z^4 := by
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_left (t*Z^4) hS
  dsimp only [k,e,n] at hscalar
  nlinarith only [hgeometry,hscalar,hcoupling,hscale]

end IntegerMultBounds.MathlibTM2.Cost
