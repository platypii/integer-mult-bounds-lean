module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaRecoveryPreparationFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRetainedCouplingFast

/-! Combine the actual retained boundary and coupling numerical work; native traffic stays explicit. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

noncomputable def replicaRecoveryPreparationNativeCost {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) : ℕ :=
  replicaBoundaryRhsCost H+replicaRecoveryInputsCost H+
    packedBoundaryRecoveryInputsCost H.metadataWidth H.span
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card H.wordWidth+
    retainedCouplingIntervalNativeCost true (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
      H.origin (H.origin+H.span) H.origin H.span H.metadataWidth+
    18*(H.span*H.wordWidth)+18+H.span*(20*H.wordWidth+26)+2

theorem replicaRecoveryPreparationNonSolve_fast_le (cw : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s),
      H.wordWidth ≤ cw*H.p →
      (replicaRecoveryPreparationNonSolveCost H : ℝ) ≤ replicaRecoveryPreparationNativeCost H+
        E*(retainedCouplingActiveRows true s H.t H.band H.origin (H.origin+H.span) H.origin H.span)*((H.band+1 : ℕ) : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨E,hE,hfast⟩ := retainedPageSpatialIntervalLoopCost_mask_fast_le cw
  refine ⟨E,hE,?_⟩
  intro s _ H hw
  have hpos : 1 ≤ H.wordWidth := by
    unfold ReplicaHaloProblem.wordWidth executionWidth
    omega
  have hh := hfast H.p H.precision H.wordWidth s H.t H.band H.origin
    (H.origin+H.span) H.origin H.span true H.p_pos hpos hw
  unfold replicaRecoveryPreparationNonSolveCost collectedReplicaRecoveryRhsCost replicaRecoveryRhsCost
  rw [preparedSharedLocalFeedCouplingIntervalCost_split]
  unfold replicaRecoveryPreparationNativeCost
  push_cast at hh ⊢
  nlinarith only [hh]

theorem batchedReplicaRecovery_numerical_fast_le (cl cw cr cV : ℕ) :
    ∃ C D E : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ E ∧
      ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) (target : ℕ)
      (X : ℕ → ZMod s → ℝ) (B : ReplicaRecoveryBatch H target X)
      (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card),
      H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p → 2^H.l ≤ cr*H.p → H.metadataWidth ≤ cV*H.p →
      H.t-s ≤ s → H.l = haloInverseRingLog s H.t →
      (batchedReplicaRecoveryTime H (B.problem htarget) : ℝ) ≤
        (initializedReplicaHaloSharedTime (B.problem htarget)+
          H.Fs.length*(replicaRecoveryPreparationNativeCost H+50*(H.span*H.wordWidth)+25*H.span+59)+
          (10*cV+19)*H.Fs.length*((haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth)+24 : ℕ)+
        (D*(replicaHaloLocalCoordinates H : ℕ)+
          C*((haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1 : ℕ)*((12*H.band+1 : ℕ) : ℝ)+
          E*(retainedCouplingActiveRows true s H.t H.band H.origin (H.origin+H.span) H.origin H.span)*((H.band+1 : ℕ) : ℝ))*H.Fs.length*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,D,hC,hD,hcaller⟩ := batchedReplicaRecovery_boundary_fast_le cl cw cr cV
  obtain ⟨E,hE,hcoupling⟩ := replicaRecoveryPreparationNonSolve_fast_le cw
  refine ⟨C,D,E,hC,hD,hE,?_⟩
  intro s _ H target X B htarget hl hw hr hV hgap hring
  have hc := hcaller H target X B htarget hl hw hr hV hgap hring
  have he := mul_le_mul_of_nonneg_left (hcoupling H hw)
    (Nat.cast_nonneg H.Fs.length : (0 : ℝ) ≤ H.Fs.length)
  push_cast at hc he ⊢
  nlinarith only [hc,he]

end IntegerMultBounds.MathlibTM2.Cost
