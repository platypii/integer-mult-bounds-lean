module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareHaloWeightFamily
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellLengthKeySetup

/-! Polynomial precision cost for the actual retained weight generator, with
linear dependence on the number of ambient coordinates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem sharedBatchWeightSetupCost_poly {P s t u q L w B Z : ℕ}
    (hZ : 1 ≤ Z) (ht : 1 ≤ t) (hs : s ≤ t) (hB : B ≤ t)
    (hP : P ≤ Z) (hu : u ≤ Z) (hq : q ≤ Z) (hL : L ≤ Z) (hw : w ≤ Z)
    (hV : weightWorkspaceWidth P q w t u ≤ Z) :
    sharedBatchWeightSetupCost P s t u q L w B ≤ 1000000*t*Z^4 := by
  let V := weightWorkspaceWidth P q w t u
  have htable : tblC V w ≤ 808*Z^2 := by
    have hwidth : V+4 ≤ 5*Z := by dsimp only [V]; omega
    have hsquare := Nat.pow_le_pow_left hwidth 2
    have hpow : Z ≤ Z^2 := by nlinarith only [hZ]
    unfold tblC
    nlinarith only [hsquare,hw,hpow]
  have hbound : sharedBatchWeightSetupCost P s t u q L w B ≤
      (((4*Z+4*Z+4*Z+19*(3*t+Z)+45)+(292*Z+4*Z+393)+
        ((Z+t+t+Z+Z+Z+0)*(4*Z+10)+42*Z+71)+(158*Z+8*Z+424)*(808*Z^2))+
        Z*(6*Z+9)+128*Z+172)+
      t*((8*Z+8)+((Z*(310*Z+124)+3)*(808*Z^2)+4*Z*Z+2)+
        (Z*(46*Z+45)+28)+12*(Z*Z)+12+50*(Z*Z)+54) := by
    unfold sharedBatchWeightSetupCost sharedWeightInitCost
    change _ ≤ _
    unfold weightWidthCost weightHeadersCost retainedWeightStepCost retainedWeightPageCost
      retainedWeightRowsCost pairLayoutCost
    dsimp only
    gcongr <;> first | exact htable | exact hV | omega
  have hpow2 : Z ≤ Z^2 := by nlinarith only [hZ]
  have hpow3 : Z^2 ≤ Z^3 := by nlinarith only [Nat.mul_le_mul_left (Z^2) hZ]
  have hpow4 : Z^3 ≤ Z^4 := by nlinarith only [Nat.mul_le_mul_left (Z^3) hZ]
  have hZ4 : 1 ≤ Z^4 := Nat.one_le_pow _ _ hZ
  have htZ := Nat.mul_le_mul_left t hpow2
  have htZ2 := Nat.mul_le_mul_left t hpow3
  have htZ3 := Nat.mul_le_mul_left t hpow4
  have hZt := Nat.mul_le_mul_left (Z^4) ht
  have ht4 := Nat.mul_le_mul_left t hZ4
  nlinarith only [hbound,hpow2,hpow3,hpow4,hZ4,htZ,htZ2,htZ3,hZt,ht4]

theorem generateHaloWeightLengthKeyCost_poly {P N q l s t u band a b L Z : ℕ}
    (hZ : 1 ≤ Z) (hs : 1 ≤ s) (hst : s < t)
    (hP : P ≤ Z) (hN : N ≤ Z) (hq : q ≤ Z) (hl : l ≤ Z) (hu : u ≤ Z)
    (hL : L ≤ Z) (hw : 2*q+8 ≤ Z)
    (hband : band ≤ t) (ha : a ≤ t) (hb : b ≤ t)
    (hV : weightWorkspaceWidth P q (2*q+8) t u ≤ Z) :
    generateHaloWeightLengthKeyCost P N q l s t u band a b
      (weightWorkspaceWidth P q (2*q+8) t u) L ≤ 2000000*t*Z^4 := by
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  let B := (haloLengthGroup s t band a b L).length
  have ht : 1 ≤ t := by omega
  have hB : B ≤ t := (haloLengthGroup_length_le s t band a b L).trans (by omega)
  have hsetup := sharedBatchWeightSetupCost_poly hZ ht hst.le hB hP hu hq hL hw hV
  have hpow2 : Z ≤ Z^2 := by nlinarith only [hZ]
  have hpow3 : Z^2 ≤ Z^3 := by nlinarith only [Nat.mul_le_mul_left (Z^2) hZ]
  have hpow4 : Z^3 ≤ Z^4 := by nlinarith only [Nat.mul_le_mul_left (Z^3) hZ]
  have htZ := Nat.mul_le_mul_left t hpow2
  have htZ2 := Nat.mul_le_mul_left t hpow3
  have htZ3 := Nat.mul_le_mul_left t hpow4
  have hZt := Nat.mul_le_mul_left (Z^2) ht
  have ht1 : t ≤ t*Z^2 := by simpa using Nat.mul_le_mul_left t (Nat.one_le_pow 2 Z hZ)
  have htable : tblC V V ≤ 808*Z^2 := by
    have hwidth : V+4 ≤ 5*Z := by dsimp only [V,w]; omega
    have hsquare := Nat.pow_le_pow_left hwidth 2
    unfold tblC
    nlinarith only [hsquare,hV,hpow2]
  have hcontrols : prepareHaloClassControlsCost P q s t u band a b L ≤ 100000*t*Z^2 := by
    have hm : prepareHaloClassControlsCost P q s t u band a b L ≤
        (4*Z+5)+(4*Z+4*Z+4*Z+19*(3*t+Z)+45)+
        ((104*Z+137)+((t+t+t+t+t+Z)*(4*Z+10)+36*Z+61)+
          ((36*t+9)*(808*Z^2)+t*(8*Z+6)+6)+(62*Z+63)) := by
      unfold prepareHaloClassControlsCost weightWidthCost preparedHaloClassCost haloClassHeadersCost
      dsimp only
      gcongr <;> first | exact htable | exact hV | exact hw | exact hB | omega
    nlinarith only [hm,hZ,ht,hpow2,htZ,hZt,ht1]
  have hcache : cacheBatchWeightPageCost B L w ≤ 100*t*Z^2 := by
    have hm : cacheBatchWeightPageCost B L w ≤
        Z*(4*Z+9)+t*(4*(Z*Z)+9)+2*(Z*Z)+22*(t*(Z*Z))+26 := by
      unfold cacheBatchWeightPageCost
      gcongr <;> first | exact hB | exact hL | exact hw
    nlinarith only [hm,hZ,ht,hpow2,htZ,hZt,ht1]
  have hsmall : 6*L+19*V+14+installHaloGroupHeadersCost P N q l s t u band a b L+
      2*(a+b+V)+7+2*(w+B)+5+28*(B*(L*w))+24+
      (2*(P+N+q+l+s+t+u+band+2*L)+21)+(2*L+2) ≤ 10000*t*Z^2 := by
    have hprod := Nat.mul_le_mul hB (Nat.mul_le_mul hL hw)
    dsimp only [installHaloGroupHeadersCost,installGroupHeadersCost]
    dsimp only [V,w] at *
    nlinarith only [hprod,hP,hN,hq,hl,hu,hL,hw,hband,ha,hb,hV,hB,hst.le,hpow2,htZ,hZt,ht1]
  change _ ≤ _ at hsetup
  dsimp only [generateHaloWeightLengthKeyCost,generateHaloWeightClassCost,generatedHaloWeightKeyCost,
    generatedHaloWeightCacheCost,generatedBatchWeightCacheCost]
  change _ ≤ _
  dsimp only [w,V,B] at hsetup hcontrols hcache hsmall
  nlinarith only [hsetup,hcontrols,hcache,hsmall,htZ2,htZ3]

theorem prepareHaloWeightFamilyCost_poly {s t : ℕ} [NeZero s]
    {P N q l u band a b Z : ℕ} (A : ℕ)
    (hZ : 1 ≤ Z) (hst : s < t)
    (hP : P ≤ Z) (hN : N ≤ Z) (hq : q ≤ Z) (hl : l ≤ Z) (hu : u ≤ Z)
    (hw : 2*q+8 ≤ Z) (hband : band ≤ t) (ha : a ≤ t) (hb : b ≤ t)
    (hV : weightWorkspaceWidth P q (2*q+8) t u ≤ Z)
    (hkeys : ∀ L ∈ haloLengthKeys s t band a b, L ≤ Z) :
    prepareHaloWeightFamilyCost A P N q l s t u band a b ≤
      initializeHaloLengthKeysBound P N q l s t u band a b+13000000*t*Z^4 := by
  let keys := haloLengthKeys s t band a b
  let V := weightWorkspaceWidth P q (2*q+8) t u
  let w := 2*q+8
  have hs : 1 ≤ s := NeZero.pos s
  have ht : 1 ≤ t := by omega
  have hlen : keys.length ≤ 6 := haloLengthKeys_length_le s t band a b
  have hcost : ∀ L ∈ keys,
      generateHaloWeightLengthKeyCost P N q l s t u band a b V L+3 ≤ 2000000*t*Z^4+3 := by
    intro L hL
    exact Nat.add_le_add_right
      (generateHaloWeightLengthKeyCost_poly hZ hs hst hP hN hq hl hu (hkeys L hL) hw hband ha hb hV) 3
  have hsum := List.sum_le_length_nsmul
    (keys.map (fun L => generateHaloWeightLengthKeyCost P N q l s t u band a b V L+3))
    (2000000*t*Z^4+3) (by
      intro x hx
      obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hx
      exact hcost L hL)
  have hsum' : (keys.map (fun L => generateHaloWeightLengthKeyCost P N q l s t u band a b V L+3)).sum ≤
      6*(2000000*t*Z^4+3) := by
    exact hsum.trans (by simpa only [List.length_map,nsmul_eq_mul,Nat.cast_id] using Nat.mul_le_mul_right (2000000*t*Z^4+3) hlen)
  have hfamily := haloWeightKeyFamily_length_le hst A w q P u band a b
  have hinit := initializeHaloLengthKeysCost_le P N q l s t u band a b
  have hZ4 : Z ≤ Z^4 := by simpa using Nat.pow_le_pow_right hZ (show 1 ≤ 4 by decide)
  have hone : 1 ≤ t*Z^4 := by simpa using Nat.mul_le_mul ht (Nat.one_le_pow 4 Z hZ)
  have hprod := Nat.mul_le_mul hst.le hw
  have hscale := Nat.mul_le_mul_left t hZ4
  have hzscale := Nat.mul_le_mul_left (Z^4) ht
  dsimp only [prepareHaloWeightFamilyCost,generateHaloWeightFamilyCost]
  change _ ≤ _
  dsimp only [keys,V,w] at hsum' hfamily hlen hprod
  nlinarith only [hsum',hfamily,hlen,hinit,hprod,hscale,hzscale,hZ4,hV,hw,hone]

end IntegerMultBounds.MathlibTM2.Cost
