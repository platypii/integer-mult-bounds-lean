module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoverySharedWorkspacePolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDistinctCoreSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoverySharedSchedule
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCompleteCachedRecoveryLocalWorkspace

/-! Shared workspace is absorbed after summing the distinct-core list. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedReplicaInteriorSharedWorkspaceSchedule_volume_le (hQ : SS.states ≤ Q)
    (R K cVratio cl cw cr cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {α : Type} (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List α) (H : α → ReplicaHaloProblem (Sizes.s n i)),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, (H r).p = Sizes.p n ∧ (H r).t = Sizes.t n i ∧ (H r).u ≤ (H r).p ∧
        (H r).l ≤ cl*(H r).p ∧ (H r).wordWidth ≤ cw*(H r).p ∧ 2^(H r).l ≤ cr*(H r).p ∧
        (H r).metadataWidth ≤ cV*(H r).p) →
      scale*(records.map (fun r => replicaInteriorSharedWorkspace (A := A) (U := U) (H r) hQ R K cVratio)).sum ≤ Sizes.T n := by
  obtain ⟨C,hpoly⟩ := replicaInteriorSharedWorkspace_axis_poly_le (A := A) (U := U) hQ R K cVratio cl cw cr cV
  filter_upwards [selectedDistinctCoreSetup_volume_le C 22 22 scale] with n hs
  intro α i _ records H hcount hparams
  apply hs i records (fun r => replicaInteriorSharedWorkspace (A := A) (U := U) (H r) hQ R K cVratio) hcount
  intro r hr
  obtain ⟨hp,ht,hu,hl,hw,hpow,hV⟩ := hparams r hr
  simpa only [hp,ht] using hpoly (H r) hu hl hw hpow hV

theorem selectedRecoveryPreparationWorkspaceSchedule_volume_le (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M cw cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {α : Type} (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List α) (H : α → ReplicaHaloProblem (Sizes.s n i)),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, (H r).p = Sizes.p n ∧ (H r).t = Sizes.t n i ∧
        (H r).wordWidth ≤ cw*(H r).p ∧ (H r).metadataWidth ≤ cV*(H r).p) →
      scale*(records.map (fun r => cachedReplicaRecoveryPreparationRowWorkspace (H r) hQ push c M)).sum ≤ Sizes.T n := by
  obtain ⟨C,hpoly⟩ := cachedRecoveryPreparationWorkspace_axis_poly_le hQ push c M cw cV
  filter_upwards [selectedDistinctCoreSetup_volume_le C 8 8 scale] with n hs
  intro α i _ records H hcount hparams
  apply hs i records (fun r => cachedReplicaRecoveryPreparationRowWorkspace (H r) hQ push c M) hcount
  intro r hr
  obtain ⟨hp,ht,hw,hV⟩ := hparams r hr
  simpa only [hp,ht] using hpoly (H r) hw hV

private theorem completeSharedWorkspaceSchedule_le {α : Type} {s : ℕ} [NeZero s]
    (records : List α) (H J : α → ReplicaHaloProblem s) (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M R K cV : ℕ) :
    (records.map (fun r => completeCachedRecoverySharedWorkspace (H r) (J r) hQ push c M R K cV)).sum ≤
      (records.map (fun r => replicaInteriorSharedWorkspace (A := A) (U := U) (H r) hQ R K cV)).sum+
      (records.map (fun r => replicaInteriorSharedWorkspace (A := A) (U := U) (J r) hQ R K cV)).sum+
      2*(records.map (fun r => cachedReplicaRecoveryPreparationRowWorkspace (H r) hQ push c M)).sum+
      mnProgPush (initializeRecoveryMasks (P := Empty) (Q := Q) (A := A) (U := U))*
        (records.map (fun r => initializeRecoveryMasksCost (H r).metadataWidth (H r).span (H r).band)).sum+
      (26+mnProgPush (initializeCouplingMasks false (P := Empty) (Q := Q) (A := A) (U := U))+
        100*preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U))*
        (records.map (fun r => cachedReplicaCouplingSharedTime (H r))).sum+
      (records.map (fun r => 48*((H r).span*(H r).wordWidth)+
        2*retainedPackedPublicationMergeCost (H r).span (H r).wordWidth+168)).sum := by
  induction records with
  | nil => simp
  | cons r records ih =>
    have hh := Nat.mul_le_mul_left (preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U))
      (cachedReplicaRecoveryHandoffSharedTime_le (H r))
    simp only [List.map_cons,List.sum_cons]
    rw [completeCachedRecoverySharedWorkspace,cachedRecoverySharedWorkspace,initializeRecoveryMasksWorkspace]
    nlinarith only [ih,hh]

/-- Both interiors, preparation scratch, masks, handoff and native controls
fit one volume reserve after summing the complete distinct-core schedule. -/
theorem selectedCompleteCachedRecoverySharedWorkspaceSchedule_volume_le (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ)
    (c M R K cVratio cl cw cr cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {α : Type} (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List α) (H J : α → ReplicaHaloProblem (Sizes.s n i)),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, ∀ G ∈ [H r,J r], G.p = Sizes.p n ∧ G.t = Sizes.t n i ∧ G.u ≤ G.p ∧
        G.l ≤ cl*G.p ∧ G.wordWidth ≤ cw*G.p ∧ 2^G.l ≤ cr*G.p ∧ G.metadataWidth ≤ cV*G.p) →
      scale*(records.map (fun r => completeCachedRecoverySharedWorkspace (H r) (J r) hQ push c M R K cVratio)).sum ≤ Sizes.T n := by
  let masks := mnProgPush (initializeRecoveryMasks (P := Empty) (Q := Q) (A := A) (U := U))
  let coupling := 26+mnProgPush (initializeCouplingMasks false (P := Empty) (Q := Q) (A := A) (U := U))+
    100*preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)
  filter_upwards [selectedReplicaInteriorSharedWorkspaceSchedule_volume_le (A := A) (U := U)
      hQ R K cVratio cl cw cr cV (6*scale),
    selectedRecoveryPreparationWorkspaceSchedule_volume_le hQ push c M cw cV (12*scale),
    selectedRecoveryMasksSchedule_volume_le cV (6*scale*masks),
    selectedCachedCouplingSharedSchedule_volume_le cw cV (6*scale*coupling),
    selectedDistinctCoreSetup_volume_le (72*cw+246) 1 1 (6*scale)] with n hi hp hm hc hs
  intro α h i _ records H J hcount hparams
  have hH r hr := hparams r hr (H r) (by simp)
  have hJ r hr := hparams r hr (J r) (by simp)
  have hfirst := hi i records H hcount hH
  have hsecond := hi i records J hcount hJ
  have hprep := hp i records H hcount (by
    intro r hr
    obtain ⟨hp,ht,_,_,hw,_,hV⟩ := hH r hr
    exact ⟨hp,ht,hw,hV⟩)
  have hmasks := hm h i records (fun r => (H r).metadataWidth) (fun r => (H r).span)
    (fun r => (H r).band) hcount (by
      intro r hr
      obtain ⟨hp,ht,_,_,_,_,hV⟩ := hH r hr
      have hspan := (H r).span_fit
      have hband : (H r).band ≤ Sizes.s n i := (H r).band_fit
      have hst := (H r).s_lt_t
      exact ⟨by omega,by omega,by simpa only [hp] using hV⟩)
  have hcoupling := hc h i records H hcount (by
    intro r hr
    obtain ⟨hp,ht,hu,_,hw,_,hV⟩ := hH r hr
    exact ⟨hp,ht,hw,hu,hV⟩)
  have hsmall := hs i records (fun r => 48*((H r).span*(H r).wordWidth)+
    2*retainedPackedPublicationMergeCost (H r).span (H r).wordWidth+168) hcount (by
      intro r hr
      obtain ⟨hp,ht,_,_,hw,_,_⟩ := hH r hr
      have hspan : (H r).span ≤ (H r).t := by have := (H r).span_fit; have := (H r).s_lt_t; omega
      have hp1 := (H r).p_pos
      have ht1 : 1 ≤ (H r).t := by have := (H r).s_lt_t; omega
      have hline := Nat.mul_le_mul hspan hw
      have hspanp := hspan.trans (Nat.le_mul_of_pos_right _ hp1)
      have hunit : 1 ≤ (H r).t*(H r).p := Nat.mul_pos ht1 hp1
      simp only [pow_one]
      rw [←hp,←ht]
      unfold retainedPackedPublicationMergeCost
      nlinarith only [hline,hspanp,hunit])
  have hsum := Nat.mul_le_mul_left scale (completeSharedWorkspaceSchedule_le records H J hQ push c M R K cVratio)
  change _ ≤ (Sizes.T n) at hmasks hcoupling
  dsimp only [masks,coupling] at hmasks hcoupling
  nlinarith only [hfirst,hsecond,hprep,hmasks,hcoupling,hsmall,hsum]

/-- Recovery problems inherit the original width profile via problem_sizing. -/
theorem selectedRawRecoveryCompleteSharedWorkspaceSchedule_volume_le (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ)
    (c M R K cVratio cl cw cr cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n))
      [NeZero (Sizes.s n i)] (records : List (RawRecoveryJob (Sizes.s n i)))
      (B : ∀ r : RawRecoveryJob (Sizes.s n i), ReplicaRecoveryBatch r.problem r.target r.solution),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.u ≤ r.problem.p ∧ r.problem.l ≤ cl*r.problem.p ∧
        r.problem.wordWidth ≤ cw*r.problem.p ∧ 2^r.problem.l ≤ cr*r.problem.p ∧
        r.problem.metadataWidth ≤ cV*r.problem.p) →
      scale*(records.map (fun r => completeCachedRecoverySharedWorkspace r.problem
        ((B r).problem r.sizing) hQ push c M R K cVratio)).sum ≤ Sizes.T n := by
  filter_upwards [selectedCompleteCachedRecoverySharedWorkspaceSchedule_volume_le hQ push c M R K cVratio cl cw cr cV scale] with n hs
  intro h i _ records B hcount hparams
  apply hs h i records (fun r => r.problem) (fun r => (B r).problem r.sizing) hcount
  intro r hr G hG
  rcases List.mem_cons.mp hG with hG | hG
  · subst G
    exact hparams r hr
  · have heq : G = (B r).problem r.sizing := by simpa only [List.mem_singleton] using hG
    subst G
    obtain ⟨hp,ht,hu,hl,hw,hpow,hV⟩ := hparams r hr
    obtain ⟨_,_,hword,hmeta⟩ := (B r).problem_sizing r.sizing
    refine ⟨hp,ht,hu,hl,?_,hpow,?_⟩
    · rw [hword]
      change r.problem.wordWidth ≤ cw*r.problem.p
      exact hw
    · rw [hmeta]
      change r.problem.metadataWidth ≤ cV*r.problem.p
      exact hV

end IntegerMultBounds.MathlibTM2.Cost
