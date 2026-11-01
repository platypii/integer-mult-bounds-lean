module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellComputedRecoveryScheduleLedger
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedCost

/-! Pairing, crop and normalization have one setup bill and a local-volume
replica bill. Reuse the existing normalization cost language. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {T A s : ℕ} [NeZero s]

noncomputable def recoveryPostprocessTime (r : PackedNormalizedJob A s) (N : ℕ) : ℕ :=
  preparedPairRecoveryOutputCost r.rawRecoveryJob N+RecoveryNormalizePlan.cropTimeCost r N

noncomputable def recoveryPostprocessReplicaTime (r : PackedNormalizedJob A s) : ℕ :=
  (16*(r.rawRecoveryJob.problem.span*r.rawRecoveryJob.problem.wordWidth)+9)+
    (packedCoreArchiveStepCost r.radius (coreLength s r.coreWidth r.k) (r.b-r.a) (2*r.q+8)+7)+
    normalizePackedReplicaCost (2*r.q+8) r.p r.W (coreLength s r.coreWidth r.k)

theorem recoveryPostprocessTime_affine (r : PackedNormalizedJob A s) (N : ℕ) :
    recoveryPostprocessTime r N = recoveryPostprocessTime r 0+N*recoveryPostprocessReplicaTime r := by
  have hq : r.q = 4*inverseExecutionExponent r.p r.l r.targetOut
      (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card (PhaseCellBand.width r.p r.u) := by
    have hq := r.hqSizing
    change r.q = executionPrecision r.p r.l (boundaryHaloTarget r.p r.u
      (boundaryRecoveryTarget r.p (r.targetOut+1)) 2
        (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card) 2 at hq
    exact hq.trans (packedRound_precision r.p r.u r.l r.targetOut _)
  have hn := preparedNormalizePackedBatchCost_affine r.Bcore r.p r.u r.l r.targetOut s r.t r.a r.b r.W N
    (coreLength s r.coreWidth r.k)
  dsimp only at hn
  have hw : 8*inverseExecutionExponent r.p r.l r.targetOut
      (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card (PhaseCellBand.width r.p r.u)+8 = 2*r.q+8 := by omega
  rw [hw] at hn
  simp only [recoveryPostprocessTime,RecoveryNormalizePlan.cropTimeCost_eq,preparedPairRecoveryOutputCost,
    generatedRecoveryCropCost,prepareRecoveryCropHeadersCost,Nat.zero_mul,Nat.zero_add]
  rw [hn]
  unfold recoveryPostprocessReplicaTime
  ring

/-- The full per-replica postprocessing bill is linear in encoded halo volume;
scalar preparation and master generation stay outside this repeated charge. -/
theorem recoveryPostprocessReplicaTime_le (r : PackedNormalizedJob A s) :
    recoveryPostprocessReplicaTime r ≤ 138*((r.b-r.a)*r.W)+62 := by
  let H := r.b-r.a
  let L := coreLength s r.coreWidth r.k
  have hH : r.radius ≤ H := by have := r.haloLength; dsimp only [H]; omega
  have hL : L ≤ H := by have := r.haloLength; dsimp only [L,H]; omega
  have hW : 1 ≤ r.W := by have := r.hW; omega
  have hnative := r.hW
  have hround := r.normalization_width
  have hnorm := normalizePackedReplicaCost_le_volume (2*r.q+8) r.p r.W L hnative hround
  have hpw : r.radius*(2*r.q+8) ≤ H*r.W :=
    (Nat.mul_le_mul_right _ hH).trans (Nat.mul_le_mul_left H hnative)
  have hLw : L*(2*r.q+8) ≤ H*r.W :=
    (Nat.mul_le_mul_right _ hL).trans (Nat.mul_le_mul_left H hnative)
  have hHw := Nat.mul_le_mul_left H hnative
  have hHunit : H ≤ H*r.W := by simpa using Nat.mul_le_mul_left H hW
  have hLW := Nat.mul_le_mul_right r.W hL
  have harchive : packedCoreArchiveStepCost r.radius L H (2*r.q+8) ≤ 37*(H*r.W)+28 := by
    unfold packedCoreArchiveStepCost retireCountedLineCost
    nlinarith only [hpw,hLw,hHw,hHunit]
  obtain ⟨_,_,hspan,hwidth,_,_,_⟩ := r.rawRecoveryJob_profile
  unfold recoveryPostprocessReplicaTime
  rw [hspan,hwidth]
  change 16*(H*(2*r.q+8))+9+(packedCoreArchiveStepCost r.radius L H (2*r.q+8)+7)+
    normalizePackedReplicaCost (2*r.q+8) r.p r.W L ≤ 138*(H*r.W)+62
  omega

/-- Replica traffic is summed by actual halo volume before any axis bound.
Only the zero-replica setup charge is repeated once per job. -/
theorem recoveryPostprocessScheduleTime_le (records : List (PackedNormalizedJob A s)) (N : ℕ)
    (hN : ∀ r ∈ records, r.Fs.length = N) :
    (records.map (fun r => recoveryPostprocessTime r r.Fs.length)).sum ≤
      (records.map (fun r => recoveryPostprocessTime r 0)).sum+
        N*(138*(records.map (fun r => (r.b-r.a)*r.W)).sum+62*records.length) := by
  induction records with
  | nil => simp
  | cons r records ih =>
    have hn := hN r (by simp)
    have ht := ih (by intro x hx; exact hN x (by simp [hx]))
    have hr := Nat.mul_le_mul_left N (recoveryPostprocessReplicaTime_le r)
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    rw [recoveryPostprocessTime_affine,hn]
    nlinarith only [hr,ht]

noncomputable def computedRecoverySetupTime (work : Fin 392 → Fin T) (r : PackedNormalizedJob A s) : ℕ :=
  r.masterInput.timeCost+recoverySeedCopyCost r.rawRecoveryJob.problem r.rawRecoveryJob.W r.Fs.length+
    completeComplexRecoveryHeadersCost r.rawRecoveryJob.problem r.Fs.length+
    recoveryDescriptorProductionCost (A := A) work r.rawRecoveryJob r.Fs.length+
    (9*(descriptorBankTape (placedDescriptorFields work (r.rawRecoveryJob.words (A := A)))).length+5)+
    retireRecoveryMastersCost r.rawRecoveryJob.problem

theorem computedRecoveryAuxiliaryTime_eq (work : Fin 392 → Fin T) (r : PackedNormalizedJob A s) :
    computedRecoveryAuxiliaryTime work r = computedRecoverySetupTime work r+
      recoveryPostprocessTime r r.Fs.length := by
  unfold computedRecoveryAuxiliaryTime computedRecoverySetupTime recoveryPostprocessTime
  omega

/-- Apply the replica-volume estimate to the actual auxiliary bills used by
computed execution. All remaining preparation and zero-replica costs stay explicit. -/
theorem computedRecoveryAuxiliaryScheduleTime_le (work : Fin 392 → Fin T)
    (records : List (PackedNormalizedJob A s)) (N : ℕ) (hN : ∀ r ∈ records, r.Fs.length = N) :
    (records.map (computedRecoveryAuxiliaryTime work)).sum ≤
      (records.map (computedRecoverySetupTime work)).sum+
        (records.map (fun r => recoveryPostprocessTime r 0)).sum+
        N*(138*(records.map (fun r => (r.b-r.a)*r.W)).sum+62*records.length) := by
  have hcost : computedRecoveryAuxiliaryTime work = fun r : PackedNormalizedJob A s =>
      computedRecoverySetupTime work r+recoveryPostprocessTime r r.Fs.length :=
    funext (computedRecoveryAuxiliaryTime_eq work)
  rw [hcost,List.sum_map_add]
  have h := recoveryPostprocessScheduleTime_le records N hN
  omega

end IntegerMultBounds.MathlibTM2.Cost
