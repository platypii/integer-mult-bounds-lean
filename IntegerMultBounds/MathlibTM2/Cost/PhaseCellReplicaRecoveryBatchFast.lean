module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryProblem
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellInitializedReplicaFast

/-! The recovery batch inherits the existing shared interior fast estimate at
the original word format. No new per-replica weight setup is charged here. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem replicaRecoveryBatchInterior_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) (target : ℕ)
      (X : ℕ → ZMod s → ℝ) (B : ReplicaRecoveryBatch H target X)
      (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card),
      H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p → 2^H.l ≤ cr*H.p → H.metadataWidth ≤ cV*H.p →
      H.t-s ≤ s → H.l = haloInverseRingLog s H.t →
      (initializedReplicaHaloTime (B.problem htarget) : ℝ) ≤
        (initializedReplicaHaloSharedTime (B.problem htarget)+H.Fs.length*(10*(H.span*H.wordWidth)+9)+
          (10*cV+19)*H.Fs.length*((haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth) : ℕ)+
        D*H.Fs.length*(replicaHaloLocalCoordinates H : ℕ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hfast⟩ := initializedReplicaHalo_fast_le cl cw cr cV
  refine ⟨D,hD,?_⟩
  intro s _ H target X B htarget hl hw hr hV hgap hring
  obtain ⟨_,_,hword,hmeta⟩ := B.problem_sizing htarget
  have hcount : (B.problem htarget).Fs.length = H.Fs.length := B.inputs_length
  have hcoords : replicaHaloLocalCoordinates (B.problem htarget) = replicaHaloLocalCoordinates H := rfl
  have hh := hfast (B.problem htarget) hl (hword.trans_le hw) hr (hmeta.trans_le hV) hgap hring
  rw [hcount,hword,hcoords] at hh
  exact hh

end IntegerMultBounds.MathlibTM2.Cost
