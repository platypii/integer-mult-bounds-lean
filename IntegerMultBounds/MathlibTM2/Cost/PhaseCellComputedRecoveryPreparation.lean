module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellComputedRecoveryPostprocess
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoveryInputStock

/-! Bound actual descriptor production/retirement and complex input preparation
through the existing shared/replica raw-input stock language. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {T A s : ℕ} [NeZero s]

noncomputable def computedRecoveryScalarTime (r : PackedNormalizedJob A s) : ℕ :=
  r.masterInput.timeCost+recoverySeedCopyCost r.rawRecoveryJob.problem r.rawRecoveryJob.W r.Fs.length+
    completeComplexRecoveryHeadersCost r.rawRecoveryJob.problem r.Fs.length+
    retireRecoveryMastersCost r.rawRecoveryJob.problem

theorem computedRecoverySetupTime_eq (work : Fin 392 → Fin T) (r : PackedNormalizedJob A s) :
    computedRecoverySetupTime work r = computedRecoveryScalarTime r+
      prepareComplexRecoveryInputCost r.rawRecoveryJob.problem.span r.rawRecoveryJob.W r.Fs.length+
      22*(descriptorBankTape (placedDescriptorFields work (r.rawRecoveryJob.words (A := A)))).length+8 := by
  unfold computedRecoverySetupTime computedRecoveryScalarTime recoveryDescriptorProductionCost
  omega

theorem computedRecoverySetupTime_le (work : Fin 392 → Fin T) (r : PackedNormalizedJob A s) :
    computedRecoverySetupTime work r ≤ computedRecoveryScalarTime r+
      44*rawRecoveryJobSharedInputStock r.rawRecoveryJob+17*((r.b-r.a)*r.W)+8676+
      r.Fs.length*(202*((r.b-r.a)*r.W)+34515) := by
  have hdescriptor : (descriptorBankTape (placedDescriptorFields work (r.rawRecoveryJob.words (A := A)))).length ≤
      2*rawRecoveryJobInputStock r.rawRecoveryJob+392 := by
    rw [placedDescriptorTape_length]
    have h := rawRecoveryJob_descriptorVolume_le (A := A) r.rawRecoveryJob
    omega
  have hN : r.rawRecoveryJob.problem.Fs.length = 2*r.Fs.length := by
    rw [r.rawRecoveryJob.fields,recoveryInputFields_length,r.rawRecoveryJob_profile.2.2.2.2.2.1,
      complexComponentFields_length]
  have hrow : rawRecoveryJobRowInputStock r.rawRecoveryJob ≤ 392+2*((r.b-r.a)*r.W) := by
    unfold rawRecoveryJobRowInputStock
    rw [r.rawRecoveryJob_profile.2.2.1,r.rawRecoveryJob_profile.2.2.2.1,r.rawRecoveryJob_profile.2.2.2.2.1]
    have h := Nat.mul_le_mul_left (r.b-r.a) r.hW
    nlinarith only [h]
  have hstock := rawRecoveryJobInputStock_affine r.rawRecoveryJob
  rw [hN] at hstock
  have hstockBound : rawRecoveryJobInputStock r.rawRecoveryJob ≤ rawRecoveryJobSharedInputStock r.rawRecoveryJob+
      2*r.Fs.length*(392+2*((r.b-r.a)*r.W)) := by
    rw [hstock]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left (2*r.Fs.length) hrow) _
  have hW : 1 ≤ r.W := by have := r.hW; omega
  have hspan : r.b-r.a ≤ (r.b-r.a)*r.W := by simpa using Nat.mul_le_mul_left (r.b-r.a) hW
  have hinput : prepareComplexRecoveryInputCost r.rawRecoveryJob.problem.span r.rawRecoveryJob.W r.Fs.length ≤
      r.Fs.length*(26*((r.b-r.a)*r.W)+19)+17*((r.b-r.a)*r.W)+44 := by
    rw [r.rawRecoveryJob_profile.2.2.1,r.rawRecoveryJob_profile.2.2.2.2.1]
    unfold prepareComplexRecoveryInputCost
    nlinarith only [hspan]
  rw [computedRecoverySetupTime_eq]
  nlinarith only [hdescriptor,hstockBound,hinput]

/-- The remaining actual auxiliary sum consists of scalar/header preparation,
zero-replica postprocessing, shared raw input stock and linear halo traffic. -/
theorem computedRecoveryAuxiliaryTime_le (work : Fin 392 → Fin T) (r : PackedNormalizedJob A s) :
    computedRecoveryAuxiliaryTime work r ≤ computedRecoveryScalarTime r+recoveryPostprocessTime r 0+
      44*rawRecoveryJobSharedInputStock r.rawRecoveryJob+17*((r.b-r.a)*r.W)+8676+
      r.Fs.length*(340*((r.b-r.a)*r.W)+34577) := by
  rw [computedRecoveryAuxiliaryTime_eq,recoveryPostprocessTime_affine]
  have hs := computedRecoverySetupTime_le work r
  have hr := Nat.mul_le_mul_left r.Fs.length (recoveryPostprocessReplicaTime_le r)
  nlinarith only [hs,hr]

private theorem recoverySeedHeader_affine (H : ReplicaHaloProblem s) (W N : ℕ) (k : Fin 392) :
    recoverySeedHeader H W N k = recoverySeedHeader H W 0 k+(if k = 390 then N else 0) := by
  by_cases hk : k = 390
  · subst k; simp [recoverySeedHeader,derivedRecoveryHeaderPorts,complexRecoveryHeader]
  · simp only [recoverySeedHeader,complexRecoveryHeader,hk,ite_false,Nat.add_zero]

theorem recoverySeedCopyCost_affine (H : ReplicaHaloProblem s) (W N : ℕ) :
    recoverySeedCopyCost H W N = recoverySeedCopyCost H W 0+4*N := by
  have hterm (k : Fin 392) : 4*recoverySeedHeader H W N k+4 =
      (4*recoverySeedHeader H W 0 k+4)+(if k = 390 then 4*N else 0) := by
    rw [recoverySeedHeader_affine]
    split_ifs <;> ring
  unfold recoverySeedCopyCost
  simp_rw [hterm]
  rw [List.sum_map_add]
  have hs : (recoverySeedHeaderPorts.map (fun k => if k = 390 then 4*N else 0)).sum = 4*N := by
    simp [recoverySeedHeaderPorts,complexRecoveryHeaderPorts,derivedRecoveryHeaderPorts]
  rw [hs]
  omega

noncomputable def computedRecoveryScalarBaseTime (r : PackedNormalizedJob A s) : ℕ :=
  r.masterInput.timeCost+recoverySeedCopyCost r.rawRecoveryJob.problem r.rawRecoveryJob.W 0+
    completeComplexRecoveryHeadersCost r.rawRecoveryJob.problem 0+retireRecoveryMastersCost r.rawRecoveryJob.problem

theorem computedRecoveryScalarTime_affine (r : PackedNormalizedJob A s) :
    computedRecoveryScalarTime r = computedRecoveryScalarBaseTime r+12*r.Fs.length := by
  unfold computedRecoveryScalarTime computedRecoveryScalarBaseTime
  rw [recoverySeedCopyCost_affine]
  unfold completeComplexRecoveryHeadersCost
  omega

/-- All remaining repeated preparation and postprocessing traffic is bounded
by the summed encoded halo volume. The residual setup sums are explicit. -/
theorem computedRecoveryAuxiliaryScheduleTime_le_preparation (work : Fin 392 → Fin T)
    (records : List (PackedNormalizedJob A s)) (N : ℕ) (hN : ∀ r ∈ records, r.Fs.length = N) :
    (records.map (computedRecoveryAuxiliaryTime work)).sum ≤
      (records.map (fun r => computedRecoveryScalarBaseTime r+recoveryPostprocessTime r 0+
        44*rawRecoveryJobSharedInputStock r.rawRecoveryJob)).sum+
      17*(records.map (fun r => (r.b-r.a)*r.W)).sum+8676*records.length+
      N*(340*(records.map (fun r => (r.b-r.a)*r.W)).sum+34589*records.length) := by
  induction records with
  | nil => simp
  | cons r records ih =>
    have hn := hN r (by simp)
    have ht := ih (by intro x hx; exact hN x (by simp [hx]))
    have hr := computedRecoveryAuxiliaryTime_le work r
    rw [computedRecoveryScalarTime_affine,hn] at hr
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hr,ht]

end IntegerMultBounds.MathlibTM2.Cost
