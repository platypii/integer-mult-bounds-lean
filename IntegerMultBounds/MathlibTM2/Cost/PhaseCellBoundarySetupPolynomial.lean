module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPagePublicationSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFactorBatchReleaseCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRetirementCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingKeyControls

/-! Explicit polynomial prices for boundary publication and retained setup bytes.
The axis-quadratic work stays in setup, outside the repeated line allowance. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem sharedPagePublicationSetupCost_poly {N V w s t Z : ℕ}
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hN : N ≤ t) (hs : s ≤ t) (hV : V ≤ Z) (hw : w ≤ Z) :
    sharedPagePublicationSetupCost N V w s ≤ 1000*t^2*Z := by
  have hm : sharedPagePublicationSetupCost N V w s ≤
      ((16*t+22)+(60*(t+1)*Z+60*t+60+(2*t+5))+t*(16*Z+9)+16)+
        (t*(t*(10*Z+29)+23*Z+54)+2*t*(Z+1)+13) := by
    unfold sharedPagePublicationSetupCost sharedPageBoundaryCoordinatesCost generatedBoundaryUnfoldCost
      generateBoundaryAdvancesCost
    gcongr
  have htt : t ≤ t^2 := by nlinarith only [ht]
  have htZ := Nat.mul_le_mul_right Z htt
  have hZt := Nat.mul_le_mul_left (t^2) hZ
  have hz := Nat.mul_le_mul_left Z ht
  nlinarith only [hm,ht,hZ,htt,htZ,hZt,hz]

theorem boundaryPermanentSizeBound_poly {q band N t Z : ℕ}
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hN : N ≤ t)
    (hq : q ≤ Z) (hw : 2*q+8 ≤ Z) (hW : 12*band+1 ≤ Z) :
    boundaryPermanentSizeBound q band N ≤ 100*t*Z^3 := by
  have htop := (Schoenhage.Schedule.topN_facts (by omega : 1 ≤ 2*q+8)).2.1
  have htop' : Schoenhage.Schedule.topN (2*q+8) ≤ 6*Z :=
    by nlinarith only [htop,hw]
  have hm : boundaryPermanentSizeBound q band N ≤
      Z+6*Z+3*Z+3*Z+Z*Z+t+(2*Z+1)*Z+(Z+1)*(2*Z+1)*Z+t*Z+2*(t*Z*Z) := by
    unfold boundaryPermanentSizeBound
    dsimp only
    gcongr
  have hp2 : Z ≤ Z^2 := by nlinarith only [hZ]
  have hp3 : Z^2 ≤ Z^3 := by nlinarith only [Nat.mul_le_mul_left (Z^2) hZ]
  have htZ := Nat.mul_le_mul_left t hp2
  have htZ2 := Nat.mul_le_mul_left t hp3
  have hZt := Nat.mul_le_mul_left (Z^3) ht
  have htt := Nat.mul_le_mul_left t hZ
  nlinarith only [hm,hZ,ht,hp2,hp3,htZ,htZ2,hZt,htt]

theorem retirePackedBandTableCost_poly {N W w t Z : ℕ}
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hN : N ≤ t) (hW : W ≤ Z) (hw : w ≤ Z) :
    retirePackedBandTableCost N W w ≤ 500*t^2*Z^2 := by
  have hc := retirePackedBandTableCost_le N W w
  have hm : retirePackedBandTableCostBound N W w ≤ t*(40*t+36*Z+12*(2*Z+1)*Z+88)+6 := by
    unfold retirePackedBandTableCostBound
    gcongr
  have hp2 : Z ≤ Z^2 := by nlinarith only [hZ]
  have ht2 : t ≤ t^2 := by nlinarith only [ht]
  have htZ := Nat.mul_le_mul_left t hp2
  have htZ2 := Nat.mul_le_mul_left (Z^2) ht2
  have ht2Z := Nat.mul_le_mul_left (t^2) hp2
  have hZt := Nat.mul_le_mul_left (t^2) hZ
  nlinarith only [hc,hm,ht,hZ,hp2,ht2,htZ,htZ2,ht2Z,hZt]

theorem placedFactorBatchReleaseCostBound_zero_poly {s N W w V D H t Z : ℕ}
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hs : s ≤ t) (hN : N ≤ t)
    (hW : W ≤ Z) (hw : w ≤ Z) (hV : V ≤ Z)
    (hD : D ≤ 100*t*Z^3) (hH : H ≤ Z^2+t*Z) :
    placedFactorBatchReleaseCostBound s 0 N W w V D H ≤ 1000000*t^2*Z^3 := by
  have hregs : sharedPageOwnedRegs.length ≤ 244 := by
    have hf := List.length_filter_le
      (fun i : Fin 240 => decide (154 ≤ i.val ∧ i.val < 224)) (List.finRange 240)
    simp only [sharedPageOwnedRegs,List.length_append,List.length_cons,List.length_nil,List.length_finRange] at *
    omega
  have hvolume : sharedPageOwnedVolumeBound s w V N D H ≤
      244*(t*Z+Z+t+100*t*Z^3+(Z^2+t*Z)+2*t*Z+1) := by
    unfold sharedPageOwnedVolumeBound
    gcongr
  have hretire := retirePackedBandTableCost_poly ht hZ hN hW hw
  have hp2 : Z ≤ Z^2 := by nlinarith only [hZ]
  have hp3 : Z^2 ≤ Z^3 := by nlinarith only [Nat.mul_le_mul_left (Z^2) hZ]
  have ht2 : t ≤ t^2 := by nlinarith only [ht]
  have htZ := Nat.mul_le_mul_left t hp2
  have htZ2 := Nat.mul_le_mul_left t hp3
  have htZ3 := Nat.mul_le_mul_left (Z^3) ht2
  have ht2Z := Nat.mul_le_mul_left (t^2) hp3
  have hZt := Nat.mul_le_mul_left (Z^3) ht
  have htz := Nat.mul_le_mul_left t hZ
  dsimp only [placedFactorBatchReleaseCostBound]
  simp only [Nat.mul_zero,Nat.zero_mul,Nat.add_zero]
  nlinarith only [hvolume,hretire,hregs,hs,ht,hZ,hp2,hp3,ht2,htZ,htZ2,htZ3,ht2Z,hZt,htz]

theorem couplingKeyReleaseCost_poly {P q s t u band a b Z : ℕ}
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hs : s ≤ t)
    (hP : P ≤ Z) (hq : q ≤ Z) (hu : u ≤ Z) (hband : band ≤ Z)
    (ha : a ≤ t) (hb : b ≤ t) (hw : 2*q+8 ≤ Z) :
    couplingKeyReleaseCost P q s t u band a b
      (couplingCoefficientPage P q s t u band a b s).length ≤ 500*t*Z^2 := by
  have hlen := couplingCoefficientPage_length_le P q s t u band a b s
  have hproduct := Nat.mul_le_mul hs (show 2*band+1 ≤ 3*Z by omega)
  have hwords : (couplingCoefficientPage P q s t u band a b s).length ≤ 3*t*Z := by
    nlinarith only [hlen,hproduct]
  have hm : couplingKeyReleaseCost P q s t u band a b
      (couplingCoefficientPage P q s t u band a b s).length ≤
      (4*Z+12*Z+4*(t+t+Z+Z+t+t)+42)+
      (2*t+2+((3*t*Z)*(12*Z+9)+12+2*(3*t*Z)+2+2*(2*Z+1)+2))+
      (2*(Z+3*Z+t+t+Z+Z+t+t)+35) := by
    unfold couplingKeyReleaseCost installCouplingHeadersCost releaseCouplingHeadersCost
      releaseCouplingPageCacheCost releaseCouplingCoefficientPageCost retireCountedLineCost
    gcongr
  have hp2 : Z ≤ Z^2 := by nlinarith only [hZ]
  have htZ := Nat.mul_le_mul_left t hp2
  have hZt := Nat.mul_le_mul_left (Z^2) ht
  have htz := Nat.mul_le_mul_left t hZ
  nlinarith only [hm,hZ,ht,hp2,htZ,hZt,htz]

end IntegerMultBounds.MathlibTM2.Cost
