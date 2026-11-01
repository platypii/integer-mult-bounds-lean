module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellComputedRecoveryPreparation
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedNormalizationWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDistinctCoreSetup

/-! The zero-replica postprocessing bill is polynomial ordinary setup. It can
be summed over cores before applying the shared selected-axis allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {A s : ℕ} [NeZero s]

theorem recoveryPostprocessTime_zero_poly (r : PackedNormalizedJob A s) (Z : ℕ)
    (hZ : 1 ≤ Z) (hB : r.Bcore ≤ Z) (hp : r.p ≤ Z) (hu : r.u ≤ Z)
    (hl : r.l ≤ Z) (htarget : r.targetOut ≤ Z) (hW : r.W ≤ Z)
    (hband : PhaseCellBand.width r.p r.u ≤ Z) (hnative : 2*r.q+8 ≤ Z) :
    recoveryPostprocessTime r 0 ≤ 2000000*r.t*Z^3 := by
  let L := coreLength s r.coreWidth r.k
  let H := r.b-r.a
  have ht : 1 ≤ r.t := by have := r.bounds.hst; omega
  have hs : s ≤ r.t := Nat.le_of_lt r.bounds.hst
  have ha : r.a ≤ r.t := r.bounds.has.trans hs
  have hb : r.b ≤ r.t := r.bounds.hbs.trans hs
  have hab : r.a+H = r.b := Nat.add_sub_of_le r.bounds.hab
  have hH : H ≤ r.t := (Nat.sub_le _ _).trans hb
  have hpart : r.radius+L ≤ r.t := by have := r.haloLength; dsimp only [L,H] at *; omega
  have hL : L ≤ r.t := by omega
  have hq : r.q = 4*inverseExecutionExponent r.p r.l r.targetOut
      (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card (PhaseCellBand.width r.p r.u) := by
    have h := r.hqSizing
    change r.q = executionPrecision r.p r.l (boundaryHaloTarget r.p r.u
      (boundaryRecoveryTarget r.p (r.targetOut+1)) 2
        (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card) 2 at h
    exact h.trans (packedRound_precision r.p r.u r.l r.targetOut _)
  have hwidth : 8*inverseExecutionExponent r.p r.l r.targetOut
      (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card (PhaseCellBand.width r.p r.u)+8 ≤ Z := by omega
  have hnorm := preparedNormalizePackedBatchCost_zero_poly ht hZ hs hB hp hW hL hband hwidth
  have hHw : H*(2*r.q+8) ≤ r.t*Z := Nat.mul_le_mul hH hnative
  have hpartw : (r.radius+L)*(2*r.q+8) ≤ r.t*Z := Nat.mul_le_mul hpart hnative
  have htZ : r.t ≤ r.t*Z := by simpa using Nat.mul_le_mul_left r.t hZ
  have hZt : Z ≤ r.t*Z := by simpa using Nat.mul_le_mul_right Z ht
  have hpair : preparedPairRecoveryOutputCost r.rawRecoveryJob 0 ≤ 100*r.t*Z := by
    unfold preparedPairRecoveryOutputCost
    rw [r.rawRecoveryJob_profile.1,r.rawRecoveryJob_profile.2.1,r.rawRecoveryJob_profile.2.2.1,
      r.rawRecoveryJob_profile.2.2.2.1]
    change prepareRecoveryPairWidthCost r.q r.a (r.a+H)+(0*(16*(H*(2*r.q+8))+9)+14)+(2*(H*(2*r.q+8))+2) ≤ _
    rw [hab]
    unfold prepareRecoveryPairWidthCost
    nlinarith only [ha,hb,hab,hH,hHw,hnative,htZ,hZt,ht,hZ]
  have hcrop : generatedRecoveryCropCost r.q r.a r.b r.radius L 0 ≤ 100*r.t*Z := by
    unfold generatedRecoveryCropCost prepareRecoveryCropHeadersCost
    simp only [Nat.zero_mul,Nat.zero_add]
    nlinarith only [ha,hb,hH,hpart,hpartw,hnative,htZ,hZt,ht,hZ]
  have hqueue : RecoveryNormalizePlan.queueTimeCost r ≤ (4*Z+4*r.t)*(4*Z+10)+64*Z+97 := by
    have hsum : (List.ofFn (RecoveryNormalizePlan.normalizationValues r)).sum ≤ 4*Z+4*r.t := by
      simpa [RecoveryNormalizePlan.normalizationValues,List.ofFn_succ,Nat.add_assoc] using
        (show r.p+r.u+r.l+r.targetOut+s+r.t+r.a+r.b ≤ 4*Z+4*r.t by omega)
    unfold RecoveryNormalizePlan.queueTimeCost
    calc
      _ ≤ (4*Z+4*r.t)*(4*r.Bcore+10)+8*(8*r.Bcore+12)+1 := by
        exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hsum) _) _
      _ ≤ _ := by
        have hm := Nat.mul_le_mul_left (4*Z+4*r.t) (show 4*r.Bcore+10 ≤ 4*Z+10 by omega)
        nlinarith only [hm,hB]
  have h₂ : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  have h₃ : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  have ht₂ := Nat.mul_le_mul_left r.t h₂
  have ht₃ := Nat.mul_le_mul_left r.t h₃
  have hZ₂t := Nat.mul_le_mul_right (Z^2) ht
  rw [recoveryPostprocessTime,RecoveryNormalizePlan.cropTimeCost_eq]
  nlinarith only [hnorm,hpair,hcrop,hqueue,hB,h₂,h₃,ht₂,ht₃,hZ₂t,htZ,hZt,ht,hZ]

/-- The complete fixed postprocessing bill is summed across cores before
spending one selected-axis setup allowance. Replicas never multiply it. -/
theorem selectedRecoveryPostprocessSetup_volume_le (cZ scale : ℕ) (hcZ : 1 ≤ cZ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List (PackedNormalizedJob A (Sizes.s n i))),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.t = Sizes.t n i ∧ r.Bcore ≤ cZ*Sizes.p n ∧ r.p ≤ cZ*Sizes.p n ∧
        r.u ≤ cZ*Sizes.p n ∧ r.l ≤ cZ*Sizes.p n ∧ r.targetOut ≤ cZ*Sizes.p n ∧
        r.W ≤ cZ*Sizes.p n ∧ PhaseCellBand.width r.p r.u ≤ cZ*Sizes.p n ∧ 2*r.q+8 ≤ cZ*Sizes.p n) →
      scale*(records.map (fun r => recoveryPostprocessTime r 0)).sum ≤ Sizes.T n := by
  filter_upwards [selectedDistinctCoreSetup_volume_le (2000000*cZ^3) 3 1 scale] with n hbound
  intro h i _ records hcount hprofile
  apply hbound i records (fun r => recoveryPostprocessTime r 0) hcount
  intro r hr
  obtain ⟨ht,hB,hp,hu,hl,htarget,hW,hband,hnative⟩ := hprofile r hr
  have hp1 : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hZ : 1 ≤ cZ*Sizes.p n := by simpa using Nat.mul_le_mul hcZ hp1
  have hcost := recoveryPostprocessTime_zero_poly r (cZ*Sizes.p n) hZ hB hp hu hl htarget hW hband hnative
  rw [ht] at hcost
  convert hcost using 1 <;> ring

end IntegerMultBounds.MathlibTM2.Cost
