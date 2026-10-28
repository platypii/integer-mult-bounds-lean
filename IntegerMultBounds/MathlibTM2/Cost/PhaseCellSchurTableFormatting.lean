module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryTableCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedAddressCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedBoundaryOrder

/-! Price the executed boundary ordering and computed-column collection. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem columnEntryStepCost_poly {q V n x R : ℕ}
    (hR : 1 ≤ R) (hq : q ≤ R) (hV : V ≤ R) (hn : n ≤ R) (hx : x ≤ R) (hw : 2*q+8 ≤ R) :
    columnEntryStepCost q V n x ≤ 1000*R^2 := by
  have hm : columnEntryStepCost q V n x ≤
      (4*R+4)+((R*(12*R+11)+27*R+6*R+36)+
        ((8*R+9)+(R*(12*R+9)+10*R+22+(2*R+2))+(2*R+2))+1) := by
    unfold columnEntryStepCost selectedColumnEntryCost copyResidentEntryCost
    gcongr
  have hp2 : R ≤ R^2 := by nlinarith only [hR]
  nlinarith only [hm,hR,hp2]

theorem columnCollectionCostBound_poly {q V s N band R : ℕ}
    (hR : 1 ≤ R) (hq : q ≤ R) (hV : V ≤ R) (hs : s ≤ R) (hN : N ≤ R)
    (hw : 2*q+8 ≤ R) (hW : 12*band+1 ≤ R) :
    columnCollectionCostBound q V s N band ≤ 100000*R^3 := by
  have hstep := columnEntryStepCost_poly hR hq hV hN hs hw
  have hband : band ≤ R := by omega
  have hc : clippedBandControlsCost N (12*band+1) N ≤ 1000*(N+(12*band+1)+N+1) := by
    have hh := packedSizeStepCost_le N (12*band+1) N
    dsimp only [packedSizeStepCost] at hh
    omega
  have hcontrols : residentBandControlsCost N band N ≤ 10000*R := by
    dsimp only [residentBandControlsCost]
    omega
  have hm : columnCollectionCostBound q V s N band ≤
      10000*R+((2*R+1)*(1000*R^2+9)+2*R+8)+
        ((8*R+9)+(R*(4*R+9)+4+((6*R*R+6)+(2*(R+R*R)+5))))+4*R+4 := by
    unfold columnCollectionCostBound retireResidentColumnCost
    dsimp only
    gcongr
  have hp2 : R ≤ R^2 := by nlinarith only [hR]
  have hp3 : R^2 ≤ R^3 := by nlinarith only [Nat.mul_le_mul_left (R^2) hR]
  nlinarith only [hm,hR,hp2,hp3]

theorem prepareBoundaryPageCost_poly {s t : ℕ} [NeZero s] {band a b R : ℕ}
    (hR : 1 ≤ R) (hs : s ≤ R) (ht : t ≤ R) (hband : band ≤ R) (ha : a ≤ R) (hb : b ≤ R)
    (hV : publicationGeometryWidth t band ≤ R) :
    prepareBoundaryPageCost s t band a b ≤ 2000000*R^3 := by
  let V := publicationGeometryWidth t band
  let N := (haloBoundary s t band a b).card
  have hN : N ≤ R := (show N ≤ s by simpa [N] using (haloBoundary s t band a b).card_le_univ).trans hs
  have horder := closedBoundaryOrderCost_le s t band a b
  have horder' : closedBoundaryOrderCost s t band a b ≤ 5000*(R+R+R+R+R+1)*(R+4)^2 := by
    apply horder.trans
    gcongr
  have hprepared : preparedBoundaryOrderCost s t band a b ≤
      closedBoundaryOrderCost s t band a b+N*(6*V+6)+4 := by
    dsimp only [preparedBoundaryOrderCost,closedBoundaryOrderCost,N,V]
    omega
  have hprod := Nat.mul_le_mul hN hV
  have hprod' := Nat.mul_le_mul (Nat.add_le_add_right hN 1) (Nat.add_le_add_right hV 1)
  have hp2 : R ≤ R^2 := by nlinarith only [hR]
  have hp3 : R^2 ≤ R^3 := by nlinarith only [Nat.mul_le_mul_left (R^2) hR]
  dsimp only [prepareBoundaryPageCost,closedBoundaryFoldCost,preparedBoundaryFoldInputsCost,boundaryFoldCountersCost]
  dsimp only [N,V] at hN hprepared hprod hprod'
  nlinarith only [horder',hprepared,hprod,hprod',hR,hs,ht,hband,ha,hb,hV,hN,hp2,hp3]

theorem constructedBoundaryTableCostBound_format_le {s t : ℕ} [NeZero s]
    (p u l a b target R : ℕ) (hR : 1 ≤ R) (hs : s ≤ R) (ht : t ≤ R)
    (hband : PhaseCellBand.width p u ≤ R) (ha : a ≤ R) (hb : b ≤ R)
    (hq : executionPrecision p l (initialSchurTarget p u target 2) 2 ≤ R)
    (hw : executionWidth p l (initialSchurTarget p u target 2) 2 ≤ R)
    (hV : publicationGeometryWidth t (PhaseCellBand.width p u) ≤ R)
    (hW : 12*PhaseCellBand.width p u+1 ≤ R) :
    let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
    constructedBoundaryTableCostBound p u l s t a b target ≤
      N*retainedIndexedColumnCost p u l s t a b target N s+3000000*R^4 := by
  dsimp only
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  have hN : N ≤ R := (show N ≤ s by simpa [N] using (haloBoundary s t (PhaseCellBand.width p u) a b).card_le_univ).trans hs
  have hwq : executionWidth p l (initialSchurTarget p u target 2) 2 =
      2*executionPrecision p l (initialSchurTarget p u target 2) 2+8 := by
    dsimp only [executionWidth,executionPrecision]; omega
  have hcollect := columnCollectionCostBound_poly hR hq hV hs hN (by rw [← hwq]; exact hw) hW
  have hprepare := prepareBoundaryPageCost_poly hR hs ht hband ha hb hV
  have hprod := Nat.mul_le_mul_left N hcollect
  have hscale := Nat.mul_le_mul_right (100000*R^3) hN
  have hp34 : R^3 ≤ R^4 := Nat.pow_le_pow_right hR (by decide)
  have hp14 : R ≤ R^4 := by simpa using Nat.pow_le_pow_right hR (show 1 ≤ 4 by decide)
  dsimp only [constructedBoundaryTableCostBound,tableColumnCostBound]
  dsimp only [N] at hN hprod hscale
  nlinarith only [hprepare,hprod,hscale,hN,hR,hp34,hp14]

end IntegerMultBounds.MathlibTM2.Cost
