module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoverySharedWorkspaceSchedule
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoveryWorkspaceLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoveryDescriptorTraffic
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryInputSchedule

/-! Sum the entire raw runStock shared allowance before volume absorption. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedRawRecoverySharedWorkspaceSchedule_volume_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ)
    (c M R K cVratio cl cw cr cV cW ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List (RawRecoveryJob (Sizes.s n i)))
      (B : ∀ r : RawRecoveryJob (Sizes.s n i), ReplicaRecoveryBatch r.problem r.target r.solution),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ r.problem.u ≤ r.problem.p ∧
        r.problem.l ≤ cl*r.problem.p ∧ r.problem.wordWidth ≤ cw*r.problem.p ∧
        2^r.problem.l ≤ cr*r.problem.p ∧ r.problem.metadataWidth ≤ cV*r.problem.p ∧
        r.W ≤ cW*r.problem.p ∧ r.problem.rhsExp = 2 ∧ 1 ≤ r.target ∧ r.target ≤ ct*Sizes.p n+1) →
      scale*(records.map (fun r => rawRecoveryJobSharedWorkspace r (B r) hR hQ push c M R K cVratio)).sum ≤ Sizes.T n := by
  let normalize := normalizeRecoveryInputPush (Q := Q) (A := A) (U := U)
  let factory := generatedReplicaBoundaryFactoryPush (A := A) (U := U) hR hQ
  obtain ⟨C,hfactory⟩ := selectedGeneratedReplicaBoundaryFactoryCost_poly_le ct
  filter_upwards [hfactory,
    selectedRawRecoverySharedInputStockSchedule_volume_le cl cw cV cW (8*scale),
    selectedRecoveryInputSharedSchedule_volume_le cw cW (4*scale*normalize),
    selectedDistinctCoreSetup_volume_le C 4 6 (4*scale*factory),
    selectedRawRecoveryCompleteSharedWorkspaceSchedule_volume_le hQ push c M R K cVratio cl cw cr cV (4*scale)]
      with n hf hi hn hfs hc
  intro h i _ records B hcount hparams
  have hinput := hi i records hcount (by
    intro r hr
    obtain ⟨hp,ht,_,hu,hl,hw,_,hV,hW,_⟩ := hparams r hr
    exact ⟨hp,ht,hl,hw,hV,hu,hW⟩)
  have hnormalize := hn i records hcount (by
    intro r hr
    obtain ⟨hp,_,_,_,_,hw,_,_,hW,_⟩ := hparams r hr
    exact ⟨hp,by simpa only [hp] using hw,by simpa only [hp] using hW⟩)
  have hcomplete := hc h i records B hcount (by
    intro r hr
    obtain ⟨hp,ht,_,hu,hl,hw,hpow,hV,_⟩ := hparams r hr
    exact ⟨hp,ht,hu,hl,hw,hpow,hV⟩)
  have hfac := hfs i records (fun r => generatedReplicaBoundaryFactoryCost r.problem r.target) hcount (by
    intro r hr
    obtain ⟨hp,ht,hl,hu,_,_,_,_,_,he,hpos,htarget⟩ := hparams r hr
    have hu' : r.problem.u ≤ Sizes.p n := by simpa only [hp] using hu
    have htarget' : r.target-1 ≤ ct*Sizes.p n := by omega
    have heq : r.target-1+1 = r.target := Nat.sub_add_cancel hpos
    have hh := hf h i r.problem (r.target-1) hp ht hl hu' htarget' he (by simpa only [heq] using r.sizing)
    simpa only [heq] using hh)
  have heq (xs : List (RawRecoveryJob (Sizes.s n i))) :
      (xs.map (fun r => rawRecoveryJobSharedWorkspace r (B r) hR hQ push c M R K cVratio)).sum =
      2*(xs.map rawRecoveryJobSharedInputStock).sum+
        normalize*(xs.map (fun r => normalizeRecoveryInputSharedTime r.problem r.W)).sum+
        factory*(xs.map (fun r => generatedReplicaBoundaryFactoryCost r.problem r.target)).sum+
        (xs.map (fun r => completeCachedRecoverySharedWorkspace r.problem ((B r).problem r.sizing)
          hQ push c M R K cVratio)).sum := by
    induction xs with
    | nil => simp
    | cons r xs ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [rawRecoveryJobSharedWorkspace,ih]
      change 2*rawRecoveryJobSharedInputStock r+normalize*normalizeRecoveryInputSharedTime r.problem r.W+
        factory*generatedReplicaBoundaryFactoryCost r.problem r.target+
        completeCachedRecoverySharedWorkspace r.problem ((B r).problem r.sizing) hQ push c M R K cVratio+_ = _
      ring
  rw [heq]
  nlinarith only [hinput,hnormalize,hfac,hcomplete]

end IntegerMultBounds.MathlibTM2.Cost
