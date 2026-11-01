module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryNativeTraffic
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaRecoveryGapFast

/-! Exact sparse interval page size connects native restoration to the same active-row geometry. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem couplingCoefficientPageInterval_length_active (P q s t u band a b origin N : ℕ) :
    (couplingCoefficientPageInterval P q s t u band a b origin N).length =
      retainedCouplingActiveRows true s t band a b origin N*(2*band+1) := by
  have hsum : (couplingCoefficientPageInterval P q s t u band a b origin N).length =
      (Finset.range N).sum (fun j => if couplingSkipAt true s t band a b (origin+j) then 0 else 2*band+1) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [couplingCoefficientPageInterval_succ,List.length_append,couplingCoefficientPageChunk_length,
        Finset.sum_range_succ,ih]
  rw [hsum,Finset.sum_ite]
  simp only [Finset.sum_const_zero,Finset.sum_const,smul_eq_mul,zero_add]
  unfold retainedCouplingActiveRows
  congr 1
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter,Bool.eq_false_iff]

theorem couplingCoefficientPageInterval_length_geometry {s t : ℕ} [NeZero s] (hst : s < t)
    (P q u band a b origin N : ℕ) (hb : b ≤ s) (hfit : origin+N ≤ s) :
    (couplingCoefficientPageInterval P q s t u band a b origin N).length ≤
      (haloBoundaryCountBound s t (2*band) a b+4*band)*(2*band+1) := by
  rw [couplingCoefficientPageInterval_length_active]
  exact Nat.mul_le_mul_right _ (retainedCouplingActiveRows_le_geometry hst true band a b origin N hb hfit)

theorem replicaRecoveryPreparationNativeCost_geometry {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :
    replicaRecoveryPreparationNativeCost H ≤ prepareCost H.precision H.wordWidth+
      20000*(H.span+H.band+haloBoundaryCountBound s H.t H.band H.origin (H.origin+H.span)+1)*
        (H.wordWidth+H.metadataWidth+tblC H.metadataWidth 1+1)+
      1000*((haloBoundaryCountBound s H.t (2*H.band) H.origin (H.origin+H.span)+4*H.band)*
        (2*H.band+1)+1)*(H.wordWidth+1) := by
  have hpage := couplingCoefficientPageInterval_length_geometry H.s_lt_t (2^15*H.p) H.precision H.u H.band
    H.origin (H.origin+H.span) H.origin H.span H.span_fit H.span_fit
  have hboundary := haloBoundary_card_bound H.s_lt_t H.band H.origin (H.origin+H.span)
  apply (replicaRecoveryPreparationNativeCost_le H).trans
  gcongr

theorem replicaRecoveryPreparationNativeCost_gap {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :
    replicaRecoveryPreparationNativeCost H ≤ prepareCost H.precision H.wordWidth+
      300000*(H.t+(H.t-s)*H.band^2)*(H.wordWidth+H.metadataWidth+tblC H.metadataWidth 1+1) := by
  let G := H.t+(H.t-s)*H.band^2
  let W := H.wordWidth+H.metadataWidth+tblC H.metadataWidth 1+1
  have ht : 1 ≤ H.t := by have := NeZero.pos s; have := H.s_lt_t; omega
  have htG : H.t ≤ G := Nat.le_add_right _ _
  have hG : 1 ≤ G := ht.trans htG
  have hcard : (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card ≤ s := by
    simpa only [ZMod.card] using (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card_le_univ
  have hrow : H.span+H.band+(haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1 ≤ 4*G := by
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
  calc
    _ ≤ _ := replicaRecoveryPreparationNativeCost_le H
    _ ≤ prepareCost H.precision H.wordWidth+20000*(4*G)*W+1000*(201*G)*W := by gcongr
    _ ≤ _ := by dsimp only [G,W]; nlinarith only [Nat.zero_le ((H.t+(H.t-s)*H.band^2)*(H.wordWidth+H.metadataWidth+tblC H.metadataWidth 1+1))]

end IntegerMultBounds.MathlibTM2.Cost
