module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedJob

/-! The constructed packet precision discharges the affine numerical cost law. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {A s : ℕ} [NeZero s]

theorem kernelTime_affine (r : PackedNormalizedJob A s) :
    r.kernelTime =
      packedKeyNormalizedBatchCost r.Bcore r.p r.q r.W r.u r.l s r.t r.a r.b r.V
        (boundaryRecoveryTarget r.p (r.targetOut+1)) (r.targetOut+1) 2 r.targetOut r.coreWidth r.k r.radius 0+
      r.Fs.length*packedKeyNormalizedReplicaCost r.p r.q r.W r.u r.l s r.t r.a r.b r.V
        (boundaryRecoveryTarget r.p (r.targetOut+1)) (r.targetOut+1) 2 r.coreWidth r.k r.radius := by
  apply packedKeyNormalizedBatchCost_affine
  rw [r.hqSizing,(boundaryHaloTarget_sizing r.p r.u r.l
    (boundaryRecoveryTarget r.p (r.targetOut+1)) 2
    (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card).1]
  rw [executionPrecision,← inverseExecutionExponent_eq]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
