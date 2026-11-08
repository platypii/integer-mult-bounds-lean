module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryJob

/-! Recovery resource counters depend on geometry and replica count, not the
chosen boundary or interior solution witnesses. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {U : Type}

namespace ReplicaHaloProblem

/-- A second pass has the original physical geometry, but its own accuracy
target and RHS exponent. Its time counter does not depend on RHS values. -/
def interiorTimeBudget (H : ReplicaHaloProblem s) (target rhsExp : ℕ) : ℕ :=
  reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)+
    (allocateZeroLineCost H.Fs.length (H.span*H.wordWidth)+
      (placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth+
        (((haloLengthKeys s H.t H.band H.origin (H.origin+H.span)).map
          (fun L => processGeneratedHaloReplicaKeyCost H.p H.l H.Fs.length H.metadataWidth
            H.origin H.span L s H.t H.u target rhsExp+3)).sum+2)))+
    realReplicaRowsCost H.Fs.length (H.span*H.wordWidth)

omit [NeZero s] in
theorem SameLayout.interiorTime_eq_budget {H J : ReplicaHaloProblem s}
    (layout : H.SameLayout J) :
    replicaRecoveryInteriorTime H J = H.interiorTimeBudget J.target J.rhsExp := by
  simp only [replicaRecoveryInteriorTime,interiorTimeBudget,ReplicaHaloProblem.keyCost,
    layout.p,layout.l,layout.count,layout.metadataWidth,layout.origin,layout.span,
    layout.wordWidth,layout.t,layout.u,layout.band]

noncomputable def interiorWorkspaceBudget (H : ReplicaHaloProblem s) (target rhsExp : ℕ)
    (hQ : SS.states ≤ Q) (R K : ℕ) : ℕ :=
  2*reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)+
    (2*allocateZeroLineCost H.Fs.length (H.span*H.wordWidth)+
      (3*placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth+
        ((haloLengthKeys s H.t H.band H.origin (H.origin+H.span)).map
          (fun L => processGeneratedHaloReplicaKeyWorkspace (A := A) (U := U) hQ R K
            H.p H.l H.Fs.length H.metadataWidth H.origin H.span L s H.t H.u target rhsExp)).sum))+
    2*realReplicaRowsCost H.Fs.length (H.span*H.wordWidth)

omit [NeZero s] in
theorem SameLayout.interiorWorkspace_eq_budget {H J : ReplicaHaloProblem s}
    (layout : H.SameLayout J) (hQ : SS.states ≤ Q) (R K : ℕ) :
    replicaRecoveryInteriorWorkspace (A := A) (U := U) H J hQ R K =
      H.interiorWorkspaceBudget (A := A) (U := U) J.target J.rhsExp hQ R K := by
  have hkeys : J.keyWorkspace (A := A) (U := U) hQ R K =
      fun L => processGeneratedHaloReplicaKeyWorkspace (A := A) (U := U) hQ R K
        H.p H.l H.Fs.length H.metadataWidth H.origin H.span L s H.t H.u J.target J.rhsExp := by
    funext L
    simp only [ReplicaHaloProblem.keyWorkspace,layout.p,layout.l,layout.count,
      layout.metadataWidth,layout.origin,layout.span,layout.t,layout.u]
  simp only [replicaRecoveryInteriorWorkspace,interiorWorkspaceBudget,hkeys,
    layout.count,layout.metadataWidth,layout.origin,layout.span,layout.wordWidth,layout.t,layout.band]

def recoveryKeyCostBudget (H : ReplicaHaloProblem s) (target L : ℕ) : ℕ :=
  processGeneratedHaloReplicaKeyCost H.p H.l H.Fs.length H.metadataWidth H.origin H.span L s H.t H.u
    (H.recoveryTarget target) H.recoveryExponent

noncomputable def recoveryKeyWorkspaceBudget (H : ReplicaHaloProblem s) (target : ℕ)
    (hQ : SS.states ≤ Q) (R K L : ℕ) : ℕ :=
  processGeneratedHaloReplicaKeyWorkspace (A := A) (U := U) hQ R K H.p H.l H.Fs.length H.metadataWidth
    H.origin H.span L s H.t H.u (H.recoveryTarget target) H.recoveryExponent

def recoveryInteriorTimeBudget (H : ReplicaHaloProblem s) (target : ℕ) : ℕ :=
  reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)+
    (allocateZeroLineCost H.Fs.length (H.span*H.wordWidth)+
      (placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth+
        (((haloLengthKeys s H.t H.band H.origin (H.origin+H.span)).map
          (fun L => H.recoveryKeyCostBudget target L+3)).sum+2)))+
    realReplicaRowsCost H.Fs.length (H.span*H.wordWidth)

noncomputable def recoveryInteriorWorkspaceBudget (H : ReplicaHaloProblem s) (target : ℕ)
    (hQ : SS.states ≤ Q) (R K : ℕ) : ℕ :=
  2*reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)+
    (2*allocateZeroLineCost H.Fs.length (H.span*H.wordWidth)+
      (3*placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth+
        ((haloLengthKeys s H.t H.band H.origin (H.origin+H.span)).map
          (fun L => H.recoveryKeyWorkspaceBudget (A := A) (U := U) target hQ R K L)).sum))+
    2*realReplicaRowsCost H.Fs.length (H.span*H.wordWidth)

end ReplicaHaloProblem

variable (H : ReplicaHaloProblem s) (target : ℕ) (X : ℕ → ZMod s → ℝ)
    (B : ReplicaRecoveryBatch H target X)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)

theorem recovery_keyCost_eq_budget (L : ℕ) :
    (B.problem htarget).keyCost L = H.recoveryKeyCostBudget target L := by
  obtain ⟨_,_,_,hmeta⟩ := B.problem_sizing htarget
  simp only [ReplicaHaloProblem.keyCost,hmeta,ReplicaHaloProblem.recoveryKeyCostBudget]
  change processGeneratedHaloReplicaKeyCost H.p H.l B.inputs.length H.metadataWidth H.origin H.span L s H.t H.u
    (H.recoveryTarget target) H.recoveryExponent = _
  rw [B.inputs_length]

theorem recovery_keyWorkspace_eq_budget (hQ : SS.states ≤ Q) (R K L : ℕ) :
    (B.problem htarget).keyWorkspace (A := A) (U := U) hQ R K L =
      H.recoveryKeyWorkspaceBudget (A := A) (U := U) target hQ R K L := by
  obtain ⟨_,_,_,hmeta⟩ := B.problem_sizing htarget
  simp only [ReplicaHaloProblem.keyWorkspace,hmeta,ReplicaHaloProblem.recoveryKeyWorkspaceBudget]
  change processGeneratedHaloReplicaKeyWorkspace (A := A) (U := U) hQ R K H.p H.l B.inputs.length
    H.metadataWidth H.origin H.span L s H.t H.u (H.recoveryTarget target) H.recoveryExponent = _
  rw [B.inputs_length]

theorem recovery_interiorTime_eq_budget :
    replicaRecoveryInteriorTime H (B.problem htarget) = H.recoveryInteriorTimeBudget target := by
  obtain ⟨_,_,hw,hmeta⟩ := B.problem_sizing htarget
  simp only [replicaRecoveryInteriorTime,ReplicaHaloProblem.recoveryInteriorTimeBudget,
    recovery_keyCost_eq_budget H target X B htarget,hw,hmeta]
  simp only [ReplicaRecoveryBatch.problem,ReplicaHaloProblem.band,ReplicaRecoveryBatch.inputs_length]

theorem recovery_interiorWorkspace_eq_budget (hQ : SS.states ≤ Q) (R K : ℕ) :
    replicaRecoveryInteriorWorkspace (A := A) (U := U) H (B.problem htarget) hQ R K =
      H.recoveryInteriorWorkspaceBudget (A := A) (U := U) target hQ R K := by
  obtain ⟨_,_,hw,hmeta⟩ := B.problem_sizing htarget
  have hkeys : (B.problem htarget).keyWorkspace (A := A) (U := U) hQ R K =
      fun L => H.recoveryKeyWorkspaceBudget (A := A) (U := U) target hQ R K L := by
    funext L
    exact recovery_keyWorkspace_eq_budget H target X B htarget hQ R K L
  simp only [replicaRecoveryInteriorWorkspace,ReplicaHaloProblem.recoveryInteriorWorkspaceBudget,hkeys,hw,hmeta]
  simp only [ReplicaRecoveryBatch.problem,ReplicaHaloProblem.band,ReplicaRecoveryBatch.inputs_length]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
