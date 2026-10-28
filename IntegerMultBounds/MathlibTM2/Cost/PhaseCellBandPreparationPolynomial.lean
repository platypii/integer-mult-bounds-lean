module

public import IntegerMultBounds.MathlibTM2.Fast.BandFactor

/-! Structural polynomial costs for numerical factor preparation, parameterized
by the supplier's multiplication bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast

theorem bandFacStepCost_poly {w B K R S : ℕ}
    (hR : 1 ≤ R) (hS : 1 ≤ S) (hw : w ≤ R) (hB : B ≤ 2*R) (hK : K ≤ R)
    (hMul : rmulCost w ≤ 288*S*R^3) :
    bandFacStepCost w B K ≤ 100000*S*R^5 := by
  have hm : bandFacStepCost w B K ≤
      100*(2*R+1)*(2*R+1)*R+200+(R*(2*(288*S*R^3)+80*R+120+6)+4)+
        (2*R*((288*S*R^3)+30*R+40+
          ((2*(2*R))*((288*S*R^3)+40*R+60)+30*R+60)+4*(2*(2*R)*R)+4*R+8+6)+4) := by
    unfold bandFacStepCost bandNewtonStepCost bandFacRowCost bandFwdStepCost
    gcongr
  have hp (j : ℕ) (hj : j ≤ 5) : R^j ≤ R^5 := Nat.pow_le_pow_right hR hj
  have hs (j : ℕ) (hj : j ≤ 5) : S*R^j ≤ S*R^5 := Nat.mul_le_mul_left S (hp j hj)
  have hRS : R^5 ≤ S*R^5 := by simpa using Nat.mul_le_mul_right (R^5) hS
  nlinarith only [hm,hp 0 (by decide),hp 1 (by decide),hp 2 (by decide),hp 3 (by decide),
    hp 4 (by decide),hs 0 (by decide),hs 1 (by decide),hs 2 (by decide),hs 3 (by decide),hs 4 (by decide),hRS]

theorem bandAxisPrepCost_poly {w k K N R S : ℕ}
    (hR : 1 ≤ R) (hS : 1 ≤ S) (hw : w ≤ R) (hk : k ≤ R) (hK : K ≤ R) (hN : N ≤ R)
    (hMul : rmulCost w ≤ 288*S*R^3) :
    bandAxisPrepCost w k K N ≤ 10000000*S*R^6 := by
  have hstep := bandFacStepCost_poly hR hS hw (by omega : k+1 ≤ 2*R) hK hMul
  have hm : bandAxisPrepCost w k K N ≤
      (4*((R+1+1)*(2*(R+1)+1)*R)+4+(2*((R+1+1)*(2*(R+1)+1)*R)+2)+
        (R*(100000*S*R^5+6)+4)+(2*((R+1+1)*(2*(R+1)+1)*R)+2))+
      ((200*(R+R+2)*(R+2)*R+2*R+200)+
        (R*((40*(R+2)*(R+2)*R+40*R+100)+6)+4+(2*((R+1)*(R+1)*R)+2)+
          (2*(R*(R+1)*R)+2)+(2*(R*(R+1)*R)+2))) := by
    unfold bandAxisPrepCost bandAxisOrgCost bandTStepCost
    gcongr
  have hp (j : ℕ) (hj : j ≤ 6) : R^j ≤ R^6 := Nat.pow_le_pow_right hR hj
  have hRS : R^6 ≤ S*R^6 := by simpa using Nat.mul_le_mul_right (R^6) hS
  nlinarith only [hm,hp 0 (by decide),hp 1 (by decide),hp 2 (by decide),hp 3 (by decide),
    hp 4 (by decide),hp 5 (by decide),hRS]

end IntegerMultBounds.MathlibTM2.Cost
