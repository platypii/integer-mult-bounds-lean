module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedJob

/-! The constructed packet precision discharges the affine numerical cost law. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
variable {A s : ℕ} [NeZero s]

/-- Packet precision agrees with the canonical selected inverse precision. -/
theorem precision_eq (r : PackedNormalizedJob A s) :
    r.q = 4*inverseExecutionExponent r.p r.l r.targetOut
      (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card (PhaseCellBand.width r.p r.u) := by
  rw [r.hqSizing,(boundaryHaloTarget_sizing r.p r.u r.l
    (boundaryRecoveryTarget r.p (r.targetOut+1)) 2
    (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card).1]
  rw [executionPrecision,← inverseExecutionExponent_eq]

noncomputable def setupTime (r : PackedNormalizedJob A s) : ℕ :=
  packedKeyNormalizedBatchCost r.Bcore r.p r.q r.W r.u r.l s r.t r.a r.b r.V
    (boundaryRecoveryTarget r.p (r.targetOut+1)) (r.targetOut+1) 2 r.targetOut r.coreWidth r.k r.radius 0

noncomputable def replicaTime (r : PackedNormalizedJob A s) : ℕ :=
  packedKeyNormalizedReplicaCost r.p r.q r.W r.u r.l s r.t r.a r.b r.V
    (boundaryRecoveryTarget r.p (r.targetOut+1)) (r.targetOut+1) 2 r.coreWidth r.k r.radius

theorem kernelTime_affine (r : PackedNormalizedJob A s) :
    r.kernelTime =
      packedKeyNormalizedBatchCost r.Bcore r.p r.q r.W r.u r.l s r.t r.a r.b r.V
        (boundaryRecoveryTarget r.p (r.targetOut+1)) (r.targetOut+1) 2 r.targetOut r.coreWidth r.k r.radius 0+
      r.Fs.length*packedKeyNormalizedReplicaCost r.p r.q r.W r.u r.l s r.t r.a r.b r.V
        (boundaryRecoveryTarget r.p (r.targetOut+1)) (r.targetOut+1) 2 r.coreWidth r.k r.radius := by
  apply packedKeyNormalizedBatchCost_affine
  exact r.precision_eq

/-- The schedule ledger keeps packet loading and cleanup explicit. Only the
numerical setup is independent of the replica count. -/
theorem scheduleTime_eq {T Q : ℕ} {U : Type} (work : Fin 325 → Fin T)
    (hR : rpStates ≤ Q)
    (hQ : SS.states ≤ Q)
    (records : List (PackedNormalizedJob A s)) :
    (records.map (fun r => r.stepTime (U := U) work hR hQ+3)).sum =
      (records.map (fun r => takeDescriptorBankCost (placedDescriptorFields work r.words)+
        r.setupTime+r.cleanup (U := U) hR hQ+3)).sum+
      (records.map (fun r => r.Fs.length*r.replicaTime)).sum := by
  induction records with
  | nil => simp
  | cons r records ih =>
    simp only [List.map_cons,List.sum_cons,stepTime] at ih ⊢
    rw [kernelTime_affine]
    dsimp only [setupTime,replicaTime] at ih ⊢
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
