module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellBatchedReplicaRecoveryFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPreparedResidual

/-! Keep repeated boundary solves at their fast row-by-bandwidth cost. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

noncomputable def replicaRecoveryPreparationNonSolveCost {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) : ℕ :=
  replicaBoundaryRhsCost H+collectedReplicaRecoveryRhsCost H

theorem replicaRecoveryPreparationRowCost_split {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :
    replicaRecoveryPreparationRowCost H = replicaRecoveryPreparationNonSolveCost H+
      preparedResidualSolveCost H.precision H.wordWidth
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (12*H.band+1) := by
  unfold replicaRecoveryPreparationRowCost replicaRecoveryPreparationNonSolveCost
  omega

theorem replicaRecoveryPreparationRow_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s),
      H.wordWidth ≤ cw*H.p →
      (replicaRecoveryPreparationRowCost H : ℝ) ≤ replicaRecoveryPreparationNonSolveCost H+
        C*((haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1 : ℕ)*
          ((12*H.band+1 : ℕ) : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := preparedResidual_fast_le cw
  refine ⟨C,hC,?_⟩
  intro s _ H hw
  have hword : H.wordWidth = 2*H.precision+8 := by
    unfold ReplicaHaloProblem.wordWidth ReplicaHaloProblem.precision executionWidth executionPrecision
    omega
  have hh := hfast H.p H.precision
    (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (12*H.band+1)
    H.p_pos (hword.symm.trans_le hw) (by omega)
  rw [←hword] at hh
  rw [replicaRecoveryPreparationRowCost_split]
  push_cast at hh ⊢
  linarith only [hh]

theorem batchedReplicaRecovery_boundary_fast_le (cl cw cr cV : ℕ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) (target : ℕ)
      (X : ℕ → ZMod s → ℝ) (B : ReplicaRecoveryBatch H target X)
      (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card),
      H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p → 2^H.l ≤ cr*H.p → H.metadataWidth ≤ cV*H.p →
      H.t-s ≤ s → H.l = haloInverseRingLog s H.t →
      (batchedReplicaRecoveryTime H (B.problem htarget) : ℝ) ≤
        (initializedReplicaHaloSharedTime (B.problem htarget)+
          H.Fs.length*(replicaRecoveryPreparationNonSolveCost H+50*(H.span*H.wordWidth)+25*H.span+59)+
          (10*cV+19)*H.Fs.length*((haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth)+24 : ℕ)+
        (D*(replicaHaloLocalCoordinates H : ℕ)+
          C*((haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1 : ℕ)*((12*H.band+1 : ℕ) : ℝ))*
          H.Fs.length*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hrow⟩ := replicaRecoveryPreparationRow_fast_le cw
  obtain ⟨D,hD,hcaller⟩ := batchedReplicaRecovery_fast_le cl cw cr cV
  refine ⟨C,D,hC,hD,?_⟩
  intro s _ H target X B htarget hl hw hr hV hgap hring
  have hc := hcaller H target X B htarget hl hw hr hV hgap hring
  have hb := mul_le_mul_of_nonneg_left (hrow H hw) (Nat.cast_nonneg H.Fs.length : (0 : ℝ) ≤ H.Fs.length)
  push_cast at hc hb ⊢
  nlinarith only [hc,hb]

end IntegerMultBounds.MathlibTM2.Cost
