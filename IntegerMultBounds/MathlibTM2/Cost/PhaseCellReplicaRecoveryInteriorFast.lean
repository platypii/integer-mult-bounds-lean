module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaRecoveryBatchFast
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryInteriorExec

/-! The executed second pass pays the existing shared interior setup once.
Archive reordering and real projection add only linear row traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s : ℕ} [NeZero s]

theorem replicaRecoveryInteriorTime_affine (H : ReplicaHaloProblem s) (target : ℕ) (X : ℕ → ZMod s → ℝ)
    (B : ReplicaRecoveryBatch H target X) htarget :
    replicaRecoveryInteriorTime H (B.problem htarget) = initializedReplicaHaloTime (B.problem htarget)+
      H.Fs.length*(28*(H.span*H.wordWidth)+28)+18 := by
  obtain ⟨_,_,hw,_⟩ := B.problem_sizing htarget
  have hc : (B.problem htarget).Fs.length = H.Fs.length := B.inputs_length
  change reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)+initializedReplicaHaloTime (B.problem htarget)+
    realReplicaRowsCost (B.problem htarget).Fs.length (H.span*(B.problem htarget).wordWidth) = _
  rw [hc,hw]
  unfold reverseCopyRowsCost realReplicaRowsCost
  ring

theorem replicaRecoveryInterior_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) (target : ℕ)
      (X : ℕ → ZMod s → ℝ) (B : ReplicaRecoveryBatch H target X)
      (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card),
      H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p → 2^H.l ≤ cr*H.p → H.metadataWidth ≤ cV*H.p →
      H.t-s ≤ s → H.l = haloInverseRingLog s H.t →
      (replicaRecoveryInteriorTime H (B.problem htarget) : ℝ) ≤
        (initializedReplicaHaloSharedTime (B.problem htarget)+H.Fs.length*(38*(H.span*H.wordWidth)+37)+
          (10*cV+19)*H.Fs.length*((haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth)+18 : ℕ)+
        D*H.Fs.length*(replicaHaloLocalCoordinates H : ℕ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hfast⟩ := replicaRecoveryBatchInterior_fast_le cl cw cr cV
  refine ⟨D,hD,?_⟩
  intro s _ H target X B htarget hl hw hr hV hgap hring
  have hh := hfast H target X B htarget hl hw hr hV hgap hring
  rw [replicaRecoveryInteriorTime_affine H target X B htarget]
  push_cast at hh ⊢
  nlinarith only [hh]

end IntegerMultBounds.MathlibTM2.Cost
