module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFirstCachedReplicaRecovery
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedCouplingSetup

/-! The first-pass/recovery handoff reuses shared setup's allowance. Archive
copying is linear per replica; cleanup and boundary controls are paid once. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

def cachedReplicaRecoveryHandoffSharedTime {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :=
  replicaCouplingNativeCleanupBound (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)+
    4*(H.span*H.wordWidth)+initializeReplicaBoundaryRhsCost H+16

theorem firstCachedReplicaRecoveryTime_split {s : ℕ} [NeZero s] (H J : ReplicaHaloProblem s) :
    firstCachedReplicaRecoveryTime H J = firstCachedReplicaPassTime H+cachedReplicaRecoveryHandoffSharedTime H+
      H.Fs.length*(22*(H.span*H.wordWidth)+19)+initializedCachedBatchedReplicaRecoveryTime H J := by
  unfold firstCachedReplicaRecoveryTime cachedReplicaRecoveryHandoffSharedTime copyRowsOrderedCost
  ring

theorem cachedReplicaRecoveryHandoffSharedTime_le {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :
    cachedReplicaRecoveryHandoffSharedTime H ≤ 100*cachedReplicaCouplingSharedTime H := by
  have hw1 : 1 ≤ H.wordWidth := by unfold ReplicaHaloProblem.wordWidth executionWidth; omega
  have htop := (Schoenhage.Schedule.topN_facts hw1).2.1
  have hcleanup : replicaCouplingNativeCleanupBound (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
      H.origin (H.origin+H.span) ≤ 10*replicaCouplingHeaderCost (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
      H.origin (H.origin+H.span) := by
    unfold replicaCouplingNativeCleanupBound replicaCouplingNativeWordBound replicaCouplingHeaderCost
    omega
  have hwV : H.wordWidth ≤ H.metadataWidth := by
    unfold ReplicaHaloProblem.metadataWidth weightWorkspaceWidth coefficientWorkspaceWidth
    omega
  have hcard : (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card ≤ H.span+2*H.band := by
    have hc := (Finset.card_le_card (Finset.sdiff_subset :
      haloVertices s H.origin (H.origin+H.span) \ interiorSet s H.t H.band ⊆
        haloVertices s H.origin (H.origin+H.span))).trans (haloVertices_card_le s H.origin (H.origin+H.span))
    have hh := (haloBoundary_card_le s H.t H.band H.origin (H.origin+H.span)).trans (Nat.add_le_add_right hc (2*H.band))
    simpa only [Nat.add_sub_cancel_left] using hh
  have hprod := Nat.mul_le_mul hcard hwV
  have hline := Nat.mul_le_mul_left H.span hwV
  have hmask : 4*(H.span*H.wordWidth)+initializeReplicaBoundaryRhsCost H+16 ≤
      100*initializeRecoveryMasksCost H.metadataWidth H.span H.band := by
    unfold initializeReplicaBoundaryRhsCost replicaBoundaryMaskCost replicaBoundaryCountersCost
      boundaryFoldCountersCost initializeRecoveryMasksCost tblC
    nlinarith only [hprod,hline,hcard,Nat.zero_le (H.span*H.metadataWidth^2),
      Nat.zero_le (H.band*H.metadataWidth^2),Nat.zero_le (H.band*H.metadataWidth)]
  unfold cachedReplicaRecoveryHandoffSharedTime cachedReplicaCouplingSharedTime initializeCachedReplicaCouplingRuntimeCost
  rw [Nat.add_sub_cancel_left]
  omega

theorem cachedReplicaRecoveryArchive_fast_le (cw : ℕ) {s : ℕ} [NeZero s]
    (H : ReplicaHaloProblem s) (hw : H.wordWidth ≤ cw*H.p) :
    ((H.Fs.length*(22*(H.span*H.wordWidth)+19) : ℕ) : ℝ) ≤
      (22*cw+19 : ℕ)*H.Fs.length*((H.t+(H.t-s)*H.band^2 : ℕ) : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  let G := H.t+(H.t-s)*H.band^2
  have hG : 1 ≤ G := by have := H.s_lt_t; dsimp only [G]; omega
  have hspan : H.span ≤ G := by have := H.span_fit; have := H.s_lt_t; dsimp only [G]; omega
  have hp : 1 ≤ H.p := H.p_pos
  have hline := Nat.mul_le_mul hspan hw
  have hunit : 1 ≤ G*H.p := Nat.mul_pos hG hp
  have hn : H.Fs.length*(22*(H.span*H.wordWidth)+19) ≤ (22*cw+19)*H.Fs.length*G*H.p := by
    have hh : 22*(H.span*H.wordWidth)+19 ≤ (22*cw+19)*G*H.p := by nlinarith only [hline,hunit]
    nlinarith only [Nat.mul_le_mul_left H.Fs.length hh]
  have hnR : ((H.Fs.length*(22*(H.span*H.wordWidth)+19) : ℕ) : ℝ) ≤
      (22*cw+19 : ℕ)*H.Fs.length*G*H.p := by exact_mod_cast hn
  have hp1 : (1 : ℝ) ≤ H.p := by exact_mod_cast hp
  have hpow := mul_le_mul_of_nonneg_left
    (Real.self_le_rpow_of_one_le hp1 (by norm_num : (1 : ℝ) ≤ 129/128))
    (by positivity : (0 : ℝ) ≤ (22*cw+19 : ℕ)*H.Fs.length*G)
  exact hnR.trans hpow

end IntegerMultBounds.MathlibTM2.Cost
