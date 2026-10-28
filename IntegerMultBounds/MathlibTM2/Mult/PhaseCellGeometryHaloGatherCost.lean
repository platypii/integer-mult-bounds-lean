module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProbeGeometryHaloGather

/-! The smaller controller fits the old caller allowance, with its tighter cost retained. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem tblC_width_gap {G W : ℕ} (hgap : G+1 ≤ W) : tblC G G+64*W ≤ tblC W W := by
  have hsq := Nat.pow_le_pow_left (by omega : G+5 ≤ W+4) 2
  dsimp only [tblC]
  nlinarith only [hsq,hgap]

theorem preparedHaloClassCost_geometry_le {G W w : ℕ} (hgap : G+10 ≤ W) (hw : w ≤ W)
    (s t band a b L : ℕ) :
    preparedHaloClassCost s t band a b L G+generateHaloGeometryWidthCost t w+20*W+64 ≤
      preparedHaloClassCost s t band a b L W := by
  have hg : G ≤ W := by omega
  have htable := tblC_width_gap (by omega : G+1 ≤ W)
  have hheader : haloClassHeadersCost s t band a b L G+40*t ≤ haloClassHeadersCost s t band a b L W := by
    have h := Nat.mul_le_mul_left (s+t+band+a+b+L) (by omega : 4*G+50 ≤ 4*W+10)
    dsimp only [haloClassHeadersCost]
    nlinarith only [h,hg,Nat.zero_le s,Nat.zero_le band,Nat.zero_le a,Nat.zero_le b,Nat.zero_le L]
  have htable' := Nat.mul_le_mul_left (36*(t-s+1)+9) htable
  have hreserve := Nat.mul_le_mul_right (64*W) (show 9 ≤ 36*(t-s+1)+9 by omega)
  have hrows := Nat.mul_le_mul_left (haloLengthGroup s t band a b L).length (by omega : 8*G+6 ≤ 8*W+6)
  dsimp only [preparedHaloClassCost,generateHaloGeometryWidthCost]
  nlinarith only [hheader,htable',hreserve,hrows,hg,hw,hgap]

theorem preparedHaloAdvanceCost_geometry_le {G W : ℕ} (hgap : G+1 ≤ W)
    (s t band a b L w : ℕ) :
    preparedHaloAdvanceCost G s t band a b L w+
      (haloLengthGroup s t band a b L).length*(10*W+10*G+23) ≤
        preparedHaloAdvanceCost W s t band a b L w := by
  have hg : G ≤ W := by omega
  have htable := tblC_width_gap hgap
  have hrow : 3*tblC G G+29*G+30+(10*W+10*G+23) ≤ 3*tblC W W+29*W+30 := by
    nlinarith only [htable,hgap,hg]
  have hrows := Nat.mul_le_mul_left (haloLengthGroup s t band a b L).length hrow
  have hwidth := Nat.mul_le_mul_left w (by omega : 4*G+10 ≤ 4*W+10)
  dsimp only [preparedHaloAdvanceCost]
  nlinarith only [hrows,hwidth,hg]

theorem probeGeometryHaloGatherCost_le_legacy {P : ℕ} (hP : 13 ≤ P)
    (q s t u band a b L : ℕ) :
    probeGeometryHaloGatherCost P q s t u band a b L ≤
      generateHaloClassControlsCost P q s t u band a b L+
        (if 0 < (haloLengthGroup s t band a b L).length then
          preparedHaloAdvanceCost (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L (2*q+8) else 0)+3 := by
  let w := 2*q+8
  let G := haloGeometryWidth t w
  let W := weightWorkspaceWidth P q w t u
  have hsize : Nat.size w ≤ w := Nat.size_le.mpr Nat.lt_two_pow_self
  have hgap : G+180 ≤ W := by
    dsimp only [G,W,haloGeometryWidth,weightWorkspaceWidth,coefficientWorkspaceWidth]
    simp only [Nat.size_zero]
    omega
  have hw : w ≤ W := by
    dsimp only [W,weightWorkspaceWidth,coefficientWorkspaceWidth]
    omega
  have hprepared := preparedHaloClassCost_geometry_le (by omega : G+10 ≤ W) hw s t band a b L
  have hadvance := preparedHaloAdvanceCost_geometry_le (by omega : G+1 ≤ W) s t band a b L w
  have hfixed : 4*G+4*W+14 ≤ 20*W+64 := by omega
  have hg : G ≤ W := by omega
  have hcost : 0 ≤ weightWidthCost P q w t u := Nat.zero_le _
  dsimp only [probeGeometryHaloGatherCost,generateHaloClassControlsCost,prepareHaloClassControlsCost,
    prepareGeometryHaloClassControlsCost,completeGeometryHaloGatherCost,widenGeometryOriginsCost]
  change (4*q+5)+generateHaloGeometryWidthCost t w+preparedHaloClassCost s t band a b L G+
    (if 0 < (haloLengthGroup s t band a b L).length then
      preparedHaloAdvanceCost G s t band a b L w+
        (weightWidthCost P q w t u+4*G+4*W+(haloLengthGroup s t band a b L).length*(10*W+10*G+23)+14)+2*(w+G)+5
    else 2*(w+G)+5)+3 ≤
    ((4*q+5)+weightWidthCost P q w t u+preparedHaloClassCost s t band a b L W+2*(w+W)+5)+
      (if 0 < (haloLengthGroup s t band a b L).length then preparedHaloAdvanceCost W s t band a b L w else 0)+3
  by_cases hB : 0 < (haloLengthGroup s t band a b L).length
  · rw [ite_eq_left hB,ite_eq_left hB]
    omega
  · rw [ite_eq_right hB,ite_eq_right hB]
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
