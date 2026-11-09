module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCyclicBoundaryPage

/-! A shared polynomial for the actual page producer, independent of replicas
and of all tape contents except the three ordinary dimension headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

private theorem boundaryOrderFromHeadersCost_poly (V s t band x y Z : ℕ)
    (hZ : 1 ≤ Z) (hV : V ≤ Z) (hs : s ≤ Z) (ht : t ≤ Z)
    (hb : band ≤ Z) (hx : x ≤ Z) (hy : y ≤ Z) :
    boundaryOrderFromHeadersCost V s t band x y ≤ 100000*Z^3 := by
  have hZsq : Z ≤ Z^2 := by nlinarith only [hZ]
  have hZcube : Z^2 ≤ Z^3 := by nlinarith only [Nat.mul_le_mul_left Z hZsq]
  have hsquare := Nat.mul_self_le_mul_self (by omega : V+4 ≤ 5*Z)
  have htable : tblC V V ≤ 808*Z^2 := by
    unfold tblC
    nlinarith only [hsquare,hV,hZsq]
  unfold boundaryOrderFromHeadersCost boundaryOrderHostCost
  calc
    _ ≤ (104*Z+137)+((Z+Z+Z+Z+Z)*(4*Z+10)+36*Z+61)+
        ((31*Z+3)*(808*Z^2)+2*Z*Z+62*Z+65) := by gcongr
    _ ≤ 100000*Z^3 := by nlinarith only [hZ,hZsq,hZcube]

theorem prepareCyclicBoundaryPageCost_poly {s A : ℕ} [NeZero s]
    (R : Regs 154 A) (t band a n Z : ℕ)
    (hZ : 1 ≤ Z) (hs : s ≤ Z) (ht : t ≤ Z) (hb : band ≤ Z)
    (ha : a ≤ s) (hn : n ≤ s) (hV : publicationGeometryWidth t band ≤ Z)
    (hsSrc : (R 121).length = s) (haSrc : (R 141).length = a) (hnSrc : (R 142).length = n) :
    prepareCyclicBoundaryPageCost R s t band a n ≤ 300000*Z^3 := by
  generalize hVeq : publicationGeometryWidth t band = V at hV
  have hN : (cyclicPrincipalBoundary s t band a n).card ≤ Z := by
    have hcard := (cyclicPrincipalBoundary s t band a n).card_le_univ
    simp only [ZMod.card] at hcard
    exact hcard.trans hs
  generalize hNeq : (cyclicPrincipalBoundary s t band a n).card = N at hN
  have haZ : a ≤ Z := ha.trans hs
  have hnZ : n ≤ Z := hn.trans hs
  have hleft : a+min n (s-a) ≤ Z := by omega
  have hright : n-min n (s-a) ≤ Z := (Nat.sub_le _ _).trans hnZ
  have hsquare := Nat.mul_self_le_mul_self (by omega : V+4 ≤ 5*Z)
  have hZsq : Z ≤ Z^2 := by nlinarith only [hZ]
  have htable : tblC V V ≤ 808*Z^2 := by
    unfold tblC
    nlinarith only [hsquare,hV,hZsq]
  have htable0 : tblC V 0 ≤ 808*Z^2 := by
    unfold tblC at htable ⊢
    omega
  have hZcube : Z^2 ≤ Z^3 := by nlinarith only [Nat.mul_le_mul_left Z hZsq]
  have hend : retainedCyclicEndpointsCost R V a n ≤ 10000*Z^2 := by
    unfold retainedCyclicEndpointsCost cyclicSplitRulersCost
    simp only [binaryHeaderQueueCost,hsSrc,haSrc,hnSrc]
    calc
      _ ≤ (4*Z+4)+
          (((((1+Z*(4*Z+10)+8*Z+12)+Z*(4*Z+10)+8*Z+12)+Z*(4*Z+10)+8*Z+12)+
              7*(4*Z+4)+3*(8*Z+8)+2+5*(808*Z^2))+
            (6*(Z+Z)+22*Z+13)+(2*(7*Z)+15)+(2*(Z+Z)+5)) := by gcongr
      _ ≤ 10000*Z^2 := by nlinarith only [hZ,hZsq]
  have hfold : closedCyclicPageFoldCost N V ≤ 1000*Z^2 := by
    unfold closedCyclicPageFoldCost boundaryFoldCountersCost
    calc
      _ ≤ Z*(4*Z+23)+26+70*(Z+1)*(Z+1)+71 := by gcongr
      _ ≤ 1000*Z^2 := by nlinarith only [hZ,hZsq]
  have hcount := Nat.mul_le_mul hN (by omega : 6*V+6 ≤ 12*Z)
  have hl := boundaryOrderFromHeadersCost_poly V s t band a (a+min n (s-a)) Z hZ hV hs ht hb haZ hleft
  have hr := boundaryOrderFromHeadersCost_poly V s t band 0 (n-min n (s-a)) Z hZ hV hs ht hb (by omega) hright
  unfold prepareCyclicBoundaryPageCost residentCyclicBoundaryOrderCost generatePublicationWidthCost
  rw [hVeq,hNeq]
  nlinarith only [hl,hr,hend,hfold,hcount,ht,hb,hZ,hZsq,hZcube]

end IntegerMultBounds.MathlibTM2.Cost
