module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellBatchedReplicaRecoveryTime
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedRecoveryCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedPreparedCost

/-! Price the executed amortized caller using the existing shared interior and retained kernels. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s : ℕ} [NeZero s]

theorem replicaRecoveryPreparationRowCost_poly (H : ReplicaHaloProblem s) {Z : ℕ}
    (hZ : 1 ≤ Z) (hq : H.precision ≤ Z) (hw : H.wordWidth ≤ Z)
    (hband : H.band ≤ Z) (hV : H.metadataWidth ≤ Z) :
    replicaRecoveryPreparationRowCost H ≤ 10000000*(ssMulConst+1)*H.t*Z^4 := by
  have ht : 1 ≤ H.t := by have := NeZero.pos s; have := H.s_lt_t; omega
  have hN : H.span ≤ H.t := by have := H.span_fit; have := H.s_lt_t; omega
  have hn : (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card ≤ H.t :=
    (show (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card ≤ s by
      simpa only [ZMod.card] using (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card_le_univ).trans H.s_lt_t.le
  have hword : H.wordWidth = 2*H.precision+8 := by
    unfold ReplicaHaloProblem.wordWidth ReplicaHaloProblem.precision executionWidth executionPrecision
    omega
  have hpos : 1 ≤ H.wordWidth := by omega
  have hsolve := preparedResidualSolveCost_poly ht hZ hn (hword.symm.trans_le hw) hband
  rw [←hword] at hsolve
  have hcoupling := preparedSharedLocalFeedCouplingIntervalCost_poly
    (P := 2^15*H.p) (s := s) (t := H.t) (u := H.u) (a := H.origin) (b := H.origin+H.span)
    (origin := H.origin) ht hZ hN hq hw hpos hband hV true
  have hinputs := packedBoundaryRecoveryInputsCost_poly ht hZ hV hN hn hw
  have hboundary : replicaBoundaryRhsCost H ≤
      stageReplicaBoundaryRhsCost H.t Z+60*(H.t+1)*Z+60*H.t+60+6*(H.t*Z)+6 := by
    dsimp only [replicaBoundaryRhsCost]
    unfold stageReplicaBoundaryRhsCost
    gcongr
  have hprepare : replicaRecoveryInputsCost H ≤ 14*(H.t*Z)+4*H.t+6*H.t+24 := by
    unfold replicaRecoveryInputsCost
    gcongr
  have hcollect : 18*(H.span*H.wordWidth)+18 ≤ 18*(H.t*Z)+18 := by gcongr
  have htZ : H.t ≤ H.t*Z := Nat.le_mul_of_pos_right _ hZ
  have hZt : Z ≤ H.t*Z := Nat.le_mul_of_pos_left _ ht
  have hunit : 1 ≤ H.t*Z := Nat.mul_pos ht hZ
  have hlinear : replicaBoundaryRhsCost H+replicaRecoveryInputsCost H+
      (18*(H.span*H.wordWidth)+18) ≤ 1000*(H.t*Z) := by
    unfold stageReplicaBoundaryRhsCost at hboundary
    nlinarith only [hboundary,hprepare,hcollect,htZ,hZt,hunit]
  have hS : 1 ≤ ssMulConst+1 := by omega
  have hpow1 : Z ≤ Z^4 := Nat.le_self_pow (by decide) Z
  have hpow2 : Z^2 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have hscale : H.t*Z^4 ≤ (ssMulConst+1)*H.t*Z^4 := by
    nlinarith only [Nat.mul_le_mul_right (H.t*Z^4) hS]
  have hs1 := (Nat.mul_le_mul_left H.t hpow1).trans hscale
  have hs2 := (Nat.mul_le_mul_left H.t hpow2).trans hscale
  unfold replicaRecoveryPreparationRowCost collectedReplicaRecoveryRhsCost replicaRecoveryRhsCost
  nlinarith only [hsolve,hcoupling,hinputs,hlinear,hs1,hs2]

theorem batchedReplicaRecoveryTime_preparation_poly (H : ReplicaHaloProblem s) (target : ℕ)
    (X : ℕ → ZMod s → ℝ) (B : ReplicaRecoveryBatch H target X) htarget {Z : ℕ}
    (hZ : 1 ≤ Z) (hq : H.precision ≤ Z) (hw : H.wordWidth ≤ Z)
    (hband : H.band ≤ Z) (hV : H.metadataWidth ≤ Z) :
    batchedReplicaRecoveryTime H (B.problem htarget) ≤ initializedReplicaHaloTime (B.problem htarget)+
      H.Fs.length*(10000000*(ssMulConst+1)*H.t*Z^4+40*(H.span*H.wordWidth)+25*H.span+50)+24 := by
  rw [batchedReplicaRecoveryTime_affine H target X B htarget]
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right
        (replicaRecoveryPreparationRowCost_poly H hZ hq hw hband hV) _) _) _)) _) _

theorem batchedReplicaRecovery_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) (target : ℕ)
      (X : ℕ → ZMod s → ℝ) (B : ReplicaRecoveryBatch H target X)
      (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card),
      H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p → 2^H.l ≤ cr*H.p → H.metadataWidth ≤ cV*H.p →
      H.t-s ≤ s → H.l = haloInverseRingLog s H.t →
      (batchedReplicaRecoveryTime H (B.problem htarget) : ℝ) ≤
        (initializedReplicaHaloSharedTime (B.problem htarget)+
          H.Fs.length*(replicaRecoveryPreparationRowCost H+50*(H.span*H.wordWidth)+25*H.span+59)+
          (10*cV+19)*H.Fs.length*((haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth)+24 : ℕ)+
        D*H.Fs.length*(replicaHaloLocalCoordinates H : ℕ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hfast⟩ := replicaRecoveryBatchInterior_fast_le cl cw cr cV
  refine ⟨D,hD,?_⟩
  intro s _ H target X B htarget hl hw hr hV hgap hring
  have hh := hfast H target X B htarget hl hw hr hV hgap hring
  rw [batchedReplicaRecoveryTime_affine H target X B htarget]
  push_cast at hh ⊢
  nlinarith only [hh]

end IntegerMultBounds.MathlibTM2.Cost
