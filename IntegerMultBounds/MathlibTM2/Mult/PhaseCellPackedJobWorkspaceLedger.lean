module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedJobTimeLedger
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierCoreStepStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedWorkspaceCost

/-! Separate the constructed job's shared numerical workspace from replica storage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
variable {A s : ℕ} [NeZero s]
namespace PackedNormalizedJob

/-- Numerical workspace retained once, independently of RHS replicas. -/
noncomputable def sharedWorkspace (r : PackedNormalizedJob A s) : ℕ :=
  packedKeyNormalizedWorkspace r.Bcore r.p r.q r.W r.u r.l s r.t r.a r.b r.V
    (boundaryRecoveryTarget r.p (r.targetOut+1)) (r.targetOut+1) 2 r.targetOut r.coreWidth r.k r.radius 0

theorem workspace_le_shared_add_payload (r : PackedNormalizedJob A s) :
    r.workspace ≤ r.sharedWorkspace+500*(r.inputPayload.length+r.Fs.length) := by
  have hq : r.q = executionPrecision r.p r.l
      (initialSchurTarget r.p r.u
        (boundaryTableBits r.p (boundaryRecoveryTarget r.p (r.targetOut+1)) 2
          (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card) 2) 2 := by
    rw [r.precision_eq,inverseExecutionExponent_eq]
    rfl
  have hrep := packedKeyWorkspaceReplicaCost_le_volume_native r.p r.q r.W r.u r.l s r.t r.a r.b
    r.targetOut r.coreWidth r.k r.radius (by rw [r.haloLength]) r.hW hq
  rw [workspace,packedKeyNormalizedWorkspace_affine]
  change r.sharedWorkspace+_ ≤ _
  have hb := Nat.mul_le_mul_left r.Fs.length hrep
  rw [inputPayload_length]
  nlinarith only [hb]

theorem persistent_le_payload (r : PackedNormalizedJob A s) :
    r.persistent ≤ 2*r.inputPayload.length+r.V := by
  rw [persistent,inputPayload_length]
  have hv := Nat.mul_le_mul_left (r.Fs.length*(r.b-r.a)) r.hW
  nlinarith only [hv]

theorem outputVolume_le_payload (r : PackedNormalizedJob A s) :
    r.outputVolume ≤ r.inputPayload.length := by
  rw [outputVolume,inputPayload_length]
  have hcore : coreLength s r.coreWidth r.k ≤ r.b-r.a := by have := r.haloLength; omega
  exact Nat.mul_le_mul_right r.W (Nat.mul_le_mul_left r.Fs.length hcore)

end PackedNormalizedJob
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
