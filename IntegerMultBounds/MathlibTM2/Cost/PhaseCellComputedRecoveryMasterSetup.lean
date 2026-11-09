module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellComputedRecoverySharedPostprocess
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawHeaderPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoverySeedCopyLedger

/-! Polynomial bounds for the actual ordinary master generation and sparse
seed/header setup, before summing the class setup allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {A s : ℕ} [NeZero s]

private theorem recoveryMasters_sum_le (r : PackedNormalizedJob A s) (Z : ℕ)
    (hZ : 1 ≤ Z) (hp : r.p ≤ Z) (hu : r.u ≤ Z) (hl : r.l ≤ Z) (htarget : r.targetOut ≤ Z)
    (hs : s ≤ Z) (ht : r.t ≤ Z) (hband : PhaseCellBand.width r.p r.u ≤ Z) :
    (List.ofFn (recoveryMasterValues r.rawRecoveryJob.problem)).sum ≤ 10*(32768*Z) := by
  have hv := inverseMasterValues_cuts_poly hZ hp hu hl htarget hs ht r.bounds.has r.bounds.hbs hband
  rw [r.rawRecoveryJob_masterValues]
  change (List.ofFn (inverseMasterValues r.p r.u r.l r.targetOut s r.t r.a r.b)).sum ≤ _
  have hsum := List.sum_le_length_nsmul (List.ofFn (inverseMasterValues r.p r.u r.l r.targetOut s r.t r.a r.b))
    (32768*Z) (by intro x hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact hv i)
  simpa only [List.length_ofFn,smul_eq_mul] using hsum

theorem computedRecoveryScalarBaseTime_poly (r : PackedNormalizedJob A s) (Z : ℕ)
    (hZ : 1 ≤ Z) (hB : r.Bcore ≤ Z) (hp : r.p ≤ Z) (hu : r.u ≤ Z) (hl : r.l ≤ Z)
    (htarget : r.targetOut ≤ Z) (hs : s ≤ Z) (ht : r.t ≤ Z) (hW : r.W ≤ Z)
    (hband : PhaseCellBand.width r.p r.u ≤ Z) (hnative : 2*r.q+8 ≤ Z) :
    computedRecoveryScalarBaseTime r ≤ (20000*32768^3+30000000)*Z^3 := by
  have hZ₂ : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  have hZ₃ : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  have ha : r.a ≤ Z := r.bounds.has.trans hs
  have hb : r.b ≤ Z := r.bounds.hbs.trans hs
  have hspan : r.b-r.a ≤ Z := (Nat.sub_le _ _).trans hb
  have hq : r.q ≤ Z := by omega
  have hprod : (r.b-r.a)*(2*r.q+8) ≤ Z^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hspan hnative
  have hatoms : inverseScalarAtoms r.p s r.t r.u r.a r.b ≤ 200*Z := by
    have hN : (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card ≤ Z := by
      exact (show (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card ≤ s by
        simpa using (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card_le_univ).trans hs
    have h₁ : Nat.size (8*r.p) ≤ 8*r.p := Nat.size_le.mpr Nat.lt_two_pow_self
    have h₂ : Nat.size (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card ≤ Z :=
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans hN
    have h₃ : Nat.size (2*PhaseCellBand.width r.p r.u+1) ≤ 2*Z+1 :=
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    dsimp only [inverseScalarAtoms,inversePrecisionAtoms]
    omega
  have hv := inverseMasterValues_cuts_poly hZ hp hu hl htarget hs ht r.bounds.has r.bounds.hbs hband
  have hheader := inverseHeaderCosts_poly (inverseMasterValues r.p r.u r.l r.targetOut s r.t r.a r.b)
    (show 1 ≤ 32768*Z by omega) (hatoms.trans (by omega)) (hB.trans (by omega)) hv
  have hmaster : r.masterInput.timeCost ≤ 20000*(32768*Z)^3+1000*Z^2 := by
    change generateInverseMastersCost r.Bcore r.p r.u r.l r.targetOut s r.t r.a r.b+(50*r.Bcore+51) ≤ _
    unfold generateInverseMastersCost
    have hqueue : (r.p+r.u+r.l+r.targetOut+s+r.t+r.a+r.b)*(4*r.Bcore+10)+278*r.Bcore+314 ≤ 1000*Z^2 := by
      have hm := Nat.mul_le_mul (show r.p+r.u+r.l+r.targetOut+s+r.t+r.a+r.b ≤ 8*Z by omega)
        (show 4*r.Bcore+10 ≤ 14*Z by omega)
      nlinarith only [hm,hB,hZ₂,hZ]
    omega
  have hsum := recoveryMasters_sum_le r Z hZ hp hu hl htarget hs ht hband
  have hheaders : completeComplexRecoveryHeadersCost r.rawRecoveryJob.problem 0 ≤ 1000000*Z^2 := by
    unfold completeComplexRecoveryHeadersCost
    rw [r.rawRecoveryJob_profile.1,r.rawRecoveryJob_profile.2.1,r.rawRecoveryJob_profile.2.2.1,
      r.rawRecoveryJob_profile.2.2.2.1]
    change (8*r.q+9)+weightWidthCost (2^15*r.p) r.q (2*r.q+8) r.t r.u+
      (4*(r.a+(r.b-r.a))+4)+(4*r.a+4)+((r.b-r.a)*(4*(2*r.q+8)+9)+4)+(8*0+9) ≤ _
    unfold weightWidthCost
    norm_num only [Nat.reducePow]
    nlinarith only [hp,hu,ht,ha,hb,hspan,hprod,hq,hnative,hZ₂,hZ]
  unfold computedRecoveryScalarBaseTime
  rw [recoverySeedCopyCost_zero_eq]
  unfold retireRecoveryMastersCost
  change r.masterInput.timeCost+(4*(List.ofFn (recoveryMasterValues r.rawRecoveryJob.problem)).sum+4*r.p+4*r.W+53)+
    completeComplexRecoveryHeadersCost r.rawRecoveryJob.problem 0+
    (2*(List.ofFn (recoveryMasterValues r.rawRecoveryJob.problem)).sum+21) ≤ _
  nlinarith only [hmaster,hsum,hheaders,hp,hW,hZ₂,hZ₃,hZ]

/-- Pay master generation, seed/header controls and retirement across the
whole class, using the existing distinct-core polynomial setup theorem. -/
theorem selectedRecoveryMasterSetup_volume_le (cZ scale : ℕ) (hcZ : 1 ≤ cZ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List (PackedNormalizedJob A (Sizes.s n i))),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.t = Sizes.t n i ∧ r.Bcore ≤ cZ*Sizes.p n ∧ r.p ≤ cZ*Sizes.p n ∧
        r.u ≤ cZ*Sizes.p n ∧ r.l ≤ cZ*Sizes.p n ∧ r.targetOut ≤ cZ*Sizes.p n ∧
        r.W ≤ cZ*Sizes.p n ∧ PhaseCellBand.width r.p r.u ≤ cZ*Sizes.p n ∧ 2*r.q+8 ≤ cZ*Sizes.p n) →
      scale*(records.map computedRecoveryScalarBaseTime).sum ≤ Sizes.T n := by
  filter_upwards [selectedDistinctCoreSetup_volume_le ((20000*32768^3+30000000)*cZ^3) 3 3 scale] with n hbound
  intro h i _ records hcount hprofile
  apply hbound i records computedRecoveryScalarBaseTime hcount
  intro r hr
  obtain ⟨ht,hB,hp,hu,hl,htarget,hW,hband,hnative⟩ := hprofile r hr
  have hp1 : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have ht1 : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have hcp : 1 ≤ cZ*Sizes.p n := by simpa using Nat.mul_le_mul hcZ hp1
  have hsmall : cZ*Sizes.p n ≤ cZ*Sizes.t n i*Sizes.p n := by
    have hm := Nat.mul_le_mul_left (cZ*Sizes.p n) ht1
    nlinarith only [hm]
  have htZ : Sizes.t n i ≤ cZ*Sizes.t n i*Sizes.p n := by
    have hm := Nat.mul_le_mul_left (Sizes.t n i) hcp
    nlinarith only [hm]
  have hsZ : Sizes.s n i ≤ cZ*Sizes.t n i*Sizes.p n := (Nat.le_of_lt (h.good.lt i)).trans htZ
  have hcost := computedRecoveryScalarBaseTime_poly r (cZ*Sizes.t n i*Sizes.p n)
    (hcp.trans hsmall) (hB.trans hsmall) (hp.trans hsmall) (hu.trans hsmall) (hl.trans hsmall)
    (htarget.trans hsmall) hsZ (by rw [ht]; exact htZ) (hW.trans hsmall) (hband.trans hsmall) (hnative.trans hsmall)
  convert hcost using 1
  ring

/-- Share a single allowance between both actual fixed setup sums. -/
theorem selectedRecoveryBaseSetup_volume_le (cZ scale : ℕ) (hcZ : 1 ≤ cZ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List (PackedNormalizedJob A (Sizes.s n i))),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.t = Sizes.t n i ∧ r.Bcore ≤ cZ*Sizes.p n ∧ r.p ≤ cZ*Sizes.p n ∧
        r.u ≤ cZ*Sizes.p n ∧ r.l ≤ cZ*Sizes.p n ∧ r.targetOut ≤ cZ*Sizes.p n ∧
        r.W ≤ cZ*Sizes.p n ∧ PhaseCellBand.width r.p r.u ≤ cZ*Sizes.p n ∧ 2*r.q+8 ≤ cZ*Sizes.p n) →
      scale*(records.map (fun r => computedRecoveryScalarBaseTime r+recoveryPostprocessTime r 0)).sum ≤ Sizes.T n := by
  filter_upwards [selectedRecoveryMasterSetup_volume_le cZ (2*scale) hcZ,
    selectedRecoveryPostprocessSetup_volume_le cZ (2*scale) hcZ] with n hm hp
  intro h i _ records hcount hprofile
  have hmaster := hm h i records hcount hprofile
  have hpost := hp h i records hcount hprofile
  rw [List.sum_map_add]
  nlinarith only [hmaster,hpost]

end IntegerMultBounds.MathlibTM2.Cost
