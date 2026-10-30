module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedKeyCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedCouplingCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloInteriorCoefficients

/-! Compose the packed key-loop comparison with the actual initial interior
coefficient pass. Arithmetic is charged once using the existing geometry bill. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem packedHaloInteriorCoefficientsCost_geometry_le {s t : ℕ} [NeZero s] (hst : s < t)
    (p l u target rhsExp a b V Z : ℕ) (hb : b ≤ s) (hZ : 1 ≤ Z)
    (hq : executionPrecision p l target rhsExp ≤ Z)
    (hw : executionWidth p l target rhsExp ≤ Z) (hV : V ≤ Z)
    (hd : ∀ L ∈ haloLengthKeys s t (PhaseCellBand.width p u) a b,
      ∀ x ∈ packedHaloKeyDimensions p l s t u target rhsExp a b V L, x ≤ Z) :
    packedHaloInteriorCoefficientsCost p l s t u target rhsExp a b V ≤
      haloInteriorCostBound p l s t u target rhsExp a b+
        sharedCouplingCoefficientIntervalCost (2^15*p) (executionPrecision p l target rhsExp)
          (executionWidth p l target rhsExp) s t u (PhaseCellBand.width p u) a b V+
        1000000*t*Z^4 := by
  have hloop := packedHaloKeyLoopCost_geometry_le hst p l u target rhsExp a b V Z hZ hd
  have hinit := initializeHaloLengthKeysCost_le (2^15*p) (executionStagePrecision p l target rhsExp+1)
    (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b
  have hsum := List.sum_le_sum (l := haloLengthCandidates s t (PhaseCellBand.width p u) a b)
    (fun L _ => show sizedClosedBatchBound p l 0 L s t u target rhsExp ≤
        haloClassSharedCost p l L s t u target rhsExp a b by
      dsimp only [haloClassSharedCost]
      omega)
  have hcell := Nat.mul_le_mul_left (t-s+1)
    (show batchCellCost p l t u target rhsExp ≤ haloClassCellCost p l t u target rhsExp by
      dsimp only [haloClassCellCost]
      omega)
  have ht : 1 ≤ t := by have := NeZero.pos s; omega
  have hN : b-a ≤ t := (Nat.sub_le b a).trans (hb.trans hst.le)
  have hdiv : (s/(t-s)+1)-2*PhaseCellBand.width p u ≤ t+1 := by
    have := Nat.div_le_self s (t-s)
    omega
  have hcontrols :
      (16*(b-a)*executionWidth p l target rhsExp+17*(b-a)+11*V+
        8*executionPrecision p l target rhsExp+2*executionWidth p l target rhsExp+36)+1+
        (2*(V+((s/(t-s)+1)-2*PhaseCellBand.width p u))+5) ≤ 1000*t*Z^2 := by
    have hmono :
        (16*(b-a)*executionWidth p l target rhsExp+17*(b-a)+11*V+
          8*executionPrecision p l target rhsExp+2*executionWidth p l target rhsExp+36)+1+
          (2*(V+((s/(t-s)+1)-2*PhaseCellBand.width p u))+5) ≤
        (16*t*Z+17*t+11*Z+8*Z+2*Z+36)+1+(2*(Z+(t+1))+5) := by gcongr
    have htZ := Nat.mul_le_mul_left t hZ
    have hZt := Nat.mul_le_mul_left Z ht
    have hpow : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
    have hscale := Nat.mul_le_mul_left t hpow
    nlinarith only [hmono,htZ,hZt,hscale,hZ,ht]
  have hpow : Z^2 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have hscale := Nat.mul_le_mul_left t hpow
  have hcontrolScale : Z^4 ≤ t*Z^4 := Nat.le_mul_of_pos_left _ ht
  have hunit : 1 ≤ t*Z^4 := Nat.mul_pos ht (one_le_pow₀ hZ)
  dsimp only [packedHaloInteriorCoefficientsCost,haloInteriorCostBound]
  nlinarith only [hloop,hinit,hsum,hcell,hcontrols,hscale,hcontrolScale,hunit]

/-- The actual initial coefficient pass satisfies the retained-family arithmetic
estimate with only polynomial extra work. -/
theorem packedHaloInteriorCoefficientsCost_weights_poly {s t : ℕ} [NeZero s] (hst : s < t)
    (p l u target rhsExp a b V Z : ℕ) (ha : a ≤ s) (hb : b ≤ s) (hZ : 1 ≤ Z)
    (hP : 2^15*p ≤ Z) (hN : executionStagePrecision p l target rhsExp+1 ≤ Z)
    (hq : executionPrecision p l target rhsExp ≤ Z) (hl : l ≤ Z) (hu : u ≤ Z)
    (hw : executionWidth p l target rhsExp ≤ Z) (hband : PhaseCellBand.width p u ≤ Z) (hV : V ≤ Z)
    (hfamilyV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ Z)
    (hlift : liftedCoefficientWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) s t u (PhaseCellBand.width p u) ≤ Z)
    (hkeys : ∀ L ∈ haloLengthCandidates s t (PhaseCellBand.width p u) a b, L ≤ Z)
    (hd : ∀ L ∈ haloLengthKeys s t (PhaseCellBand.width p u) a b,
      ∀ x ∈ packedHaloKeyDimensions p l s t u target rhsExp a b V L, x ≤ Z) :
    packedHaloInteriorCoefficientsCost p l s t u target rhsExp a b V ≤
      familyHaloInteriorGeometryCost p l s t u target rhsExp a b+22000000*t*Z^4 := by
  have hcoeff := packedHaloInteriorCoefficientsCost_geometry_le hst p l u target rhsExp a b V Z hb hZ hq hw hV hd
  have hscalar := haloInteriorCostBound_weights_poly p l u target rhsExp a b Z hst hZ hP hN hq hl hu hw
    hfamilyV hkeys
  have ht : 1 ≤ t := by have := NeZero.pos s; omega
  have hcoupling := sharedCouplingCoefficientIntervalCost_poly ht hZ hst.le ha hb hP hq hw hu hband hV hlift
  nlinarith only [hcoeff,hscalar,hcoupling]

end IntegerMultBounds.MathlibTM2.Cost
