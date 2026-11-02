module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreGatherTraffic
public import IntegerMultBounds.NLogN.PhaseCellCoreGatherVolume

/-! Actual restoring replica exposure has linear source traffic. Use the real
core count directly; no archive capacity or padding factor is assumed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

def coreExposureTrafficFactor (cV cW : ℕ) : ℕ := coreGatherTrafficFactor cV cW+120

theorem replicaCoreGatherStepCost_le_source (cV cW p V s width radius L w : ℕ)
    (hVpos : 1 ≤ V) (hs : 1 ≤ s) (hw : 1 ≤ w) (hwidth : 0 < width)
    (hwidthS : width ≤ s) (hradius : radius ≤ width) (hprepare : p^2 ≤ width) (hL : L ≤ s)
    (hV : V ≤ cV*p) (hW : w ≤ cW*p)
    (hcores : 0 < (coreGatherIndices s width radius L).length) :
    replicaCoreGatherStepCost V s width radius L w ≤ coreExposureTrafficFactor cV cW*(s*w) := by
  have hstep := replicaCoreGatherStepCost_le cV cW p V s width radius L w
    (coreGatherIndices s width radius L).length hVpos hs hw hwidth hwidthS hprepare hL hV hW hcores le_rfl
  have hvolume := Nat.mul_le_mul_right w (coreGather_volume_le_six s width radius L hwidthS hradius)
  unfold coreExposureTrafficFactor
  nlinarith only [hstep,hvolume]

theorem replicaCoreExposureCosts_le_source (cV cW p V s width radius L w B : ℕ)
    (hVpos : 1 ≤ V) (hs : 1 ≤ s) (hw : 1 ≤ w) (hwidth : 0 < width)
    (hwidthS : width ≤ s) (hradius : radius ≤ width) (hprepare : p^2 ≤ width) (hL : L ≤ s)
    (hV : V ≤ cV*p) (hW : w ≤ cW*p) (hB : 0 < B)
    (hcores : 0 < (coreGatherIndices s width radius L).length) :
    replicaCoreGatherLoopCost V s width radius L w B ≤ (coreExposureTrafficFactor cV cW+7)*(B*s*w)+6 ∧
    B*(coreGatherIndices s width radius L).length*L*w+3*(replicaCoreGatherStepCost V s width radius L w+2) ≤
      (3*coreExposureTrafficFactor cV cW+6)*(B*s*w)+6 := by
  have hstep := replicaCoreGatherStepCost_le_source cV cW p V s width radius L w
    hVpos hs hw hwidth hwidthS hradius hprepare hL hV hW hcores
  have hvolume := Nat.mul_le_mul_right w (coreGather_volume_le_six s width radius L hwidthS hradius)
  have hscaled := Nat.mul_le_mul_left B hstep
  have hscaledVolume := Nat.mul_le_mul_left B hvolume
  have hsw : 1 ≤ s*w := Nat.mul_le_mul hs hw
  have hBunit : B ≤ B*(s*w) := Nat.le_mul_of_pos_right _ (by omega)
  have hsource : s*w ≤ B*s*w := by
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_left (s*w) hB
  have hreserve := Nat.mul_le_mul_left (3*coreExposureTrafficFactor cV cW) hsource
  constructor
  · unfold replicaCoreGatherLoopCost
    nlinarith only [hscaled,hBunit]
  · nlinarith only [hstep,hscaledVolume,hreserve]

end IntegerMultBounds.MathlibTM2.Cost
