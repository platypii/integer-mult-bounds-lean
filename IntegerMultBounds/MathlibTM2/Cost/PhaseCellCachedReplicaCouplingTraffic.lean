module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaLocalCoupling
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryNativeGeometry

/-! Cached first-pass coupling has linear native stream traffic. Geometry table
work is excluded from the repeated row and must be paid by shared mask setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem cachedReplicaLocalCouplingCost_le (boundary : Bool) (P q w s t u band a b origin N V : ℕ) :
    cachedReplicaLocalCouplingCost boundary P q w s t u band a b origin N V ≤
      10000*(N+band+1)*(w+V+1)+
        1000*((couplingCoefficientPageInterval P q s t u band a b origin N).length+1)*(w+1)+
        retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N := by
  unfold cachedReplicaLocalCouplingCost cachedGatheredRibbonCost maskCouplingSourceCost transferCountedLineCost
  ring_nf
  omega

theorem cachedReplicaLocalCouplingCost_gap {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) (boundary : Bool) :
    cachedReplicaLocalCouplingCost boundary (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
      H.origin (H.origin+H.span) H.origin H.span H.metadataWidth ≤
      300000*(H.t+(H.t-s)*H.band^2)*(H.wordWidth+H.metadataWidth+1)+
        retainedPageSpatialIntervalLoopCost boundary H.precision H.wordWidth s H.t H.band
          H.origin (H.origin+H.span) H.origin H.span := by
  let G := H.t+(H.t-s)*H.band^2
  let W := H.wordWidth+H.metadataWidth+1
  have ht : 1 ≤ H.t := by have := H.s_lt_t; omega
  have htG : H.t ≤ G := Nat.le_add_right _ _
  have hG : 1 ≤ G := ht.trans htG
  have hrow : H.span+H.band+1 ≤ 3*G := by
    have := H.span_fit
    have hband : H.band ≤ s := H.band_fit
    have := H.s_lt_t
    omega
  have hpage := couplingCoefficientPageInterval_length_geometry H.s_lt_t (2^15*H.p) H.precision H.u H.band
    H.origin (H.origin+H.span) H.origin H.span H.span_fit H.span_fit
  have hvolume := familyKernelVolume_le (a := H.origin) (b := H.origin+H.span) H.s_lt_t
    (NLogN.PhaseCellBand.width_pos H.p H.u)
  have howned : (haloBoundaryCountBound s H.t (2*H.band) H.origin (H.origin+H.span)+4*H.band)*(2*H.band+1) ≤
      familyKernelVolume s H.t H.band H.origin (H.origin+H.span) := by unfold familyKernelVolume; omega
  have hlength : (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band
      H.origin (H.origin+H.span) H.origin H.span).length+1 ≤ 201*G := by
    have hh := hpage.trans (howned.trans hvolume)
    change _ ≤ 200*G at hh
    omega
  have hwidth : H.wordWidth+1 ≤ W := by dsimp only [W]; omega
  have ha := Nat.mul_le_mul hrow (le_refl W)
  have hb := Nat.mul_le_mul hlength hwidth
  have hc := cachedReplicaLocalCouplingCost_le boundary (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
    H.origin (H.origin+H.span) H.origin H.span H.metadataWidth
  change _ ≤ 300000*G*W+_
  change _ ≤ (10000*(H.span+H.band+1)*W+_)+_ at hc
  nlinarith only [hc,ha,hb]

end IntegerMultBounds.MathlibTM2.Cost
