module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCouplingSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingCoefficientInterval

/-! Price packed interval coefficient generation using the existing coefficient
row and packet estimates. No arithmetic certificate is regenerated. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem sharedCouplingCoefficientIntervalCost_poly {P q w s t u band a b V Z : ℕ}
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hs : s ≤ t) (ha : a ≤ s) (hb : b ≤ s)
    (hP : P ≤ Z) (hq : q ≤ Z) (hw : w ≤ Z) (hu : u ≤ Z) (hband : band ≤ Z)
    (hV : V ≤ Z) (hlift : liftedCoefficientWidth P q w s t u band ≤ Z) :
    sharedCouplingCoefficientIntervalCost P q w s t u band a b V ≤ 10000000*t*Z^4 := by
  let N := b-a
  have hN : N ≤ t := (Nat.sub_le b a).trans (hb.trans hs)
  have haT := ha.trans hs
  have hpacket := buildMarkedRowCoefficientPacketCost_origin_poly ht hZ hs ha hP hq hw hu hband hlift
  have hloop := couplingCoefficientPageIntervalLoopCost_poly (a := a) (b := b) (origin := a)
    hZ hP hw hband hlift N
  have hlen := couplingCoefficientPageInterval_length_le P q s t u band a b a N
  have hprod := Nat.mul_le_mul hN (show 2*band+1 ≤ 3*Z by omega)
  have hwords : (couplingCoefficientPageInterval P q s t u band a b a N).length ≤ 3*t*Z := by
    nlinarith only [hlen,hprod]
  have htransfer : transferCountedLineCost
      (couplingCoefficientPageInterval P q s t u band a b a N).length w ≤ (3*t*Z)*(10*Z+9)+10 := by
    unfold transferCountedLineCost
    gcongr
  have hloop' := hloop.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hN) 2)
  have hcontrols :
      6*a+6+8*N+11*V+8+prepareCouplingPageCountsCost N band+144*V+145+
        ((46*N+2)*tblC V 1+66*V+2*N+70)+24*liftedCoefficientWidth P q w s t u band+4 ≤
          100000*t*Z^3 := by
    have hmono :
        6*a+6+8*N+11*V+8+prepareCouplingPageCountsCost N band+144*V+145+
          ((46*N+2)*tblC V 1+66*V+2*N+70)+24*liftedCoefficientWidth P q w s t u band+4 ≤
        6*t+6+8*t+11*Z+8+prepareCouplingPageCountsCost t Z+144*Z+145+
          ((46*t+2)*tblC Z 1+66*Z+2*t+70)+24*Z+4 := by
      unfold prepareCouplingPageCountsCost tblC
      gcongr
    apply hmono.trans
    unfold prepareCouplingPageCountsCost tblC
    have h₂ : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
    have h₃ : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
    have ht₂ := Nat.mul_le_mul_left t h₂
    have ht₃ := Nat.mul_le_mul_left t h₃
    have hZt := Nat.mul_le_mul_left (Z^3) ht
    have htZ := Nat.mul_le_mul_left t hZ
    nlinarith only [ht,hZ,h₂,h₃,ht₂,ht₃,hZt,htZ]
  have h₃₄ : Z^3 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have ht₃₄ := Nat.mul_le_mul_left t h₃₄
  have h₂₃ : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  have ht₂₃ := Nat.mul_le_mul_left t h₂₃
  have h₁₂ : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  have ht₁₂ := Nat.mul_le_mul_left t h₁₂
  have hunit : 1 ≤ t*Z := Nat.mul_pos ht hZ
  dsimp only [sharedCouplingCoefficientIntervalCost]
  dsimp only [N] at hcontrols hloop' htransfer
  nlinarith only [hpacket,hloop',htransfer,hcontrols,ht₃₄,ht₂₃,ht₁₂,hunit]

end IntegerMultBounds.MathlibTM2.Cost
