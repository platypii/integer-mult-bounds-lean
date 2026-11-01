module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoverySharedWorkspaceSchedule

/-! Summed raw workspace also pays restoring cleanup, retaining exponent-one
precision and actual local numerical volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

private theorem sum_map_shared_le {α : Type} (records : List α) (cost shared volume : α → ℕ)
    (C : ℕ) (h : ∀ r ∈ records, cost r ≤ shared r+C*volume r) :
    (records.map cost).sum ≤ (records.map shared).sum+C*(records.map volume).sum := by
  induction records with
  | nil => simp
  | cons r records ih =>
    have hr := h r (by simp)
    have hs := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons]
    nlinarith only [hr,hs]

theorem selectedRawRecoveryRunStock_sum_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ)
    (c M R K cVratio cl cw cr cV cW ct scale : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List (RawRecoveryJob (Sizes.s n i)))
      (B : ∀ r : RawRecoveryJob (Sizes.s n i), ReplicaRecoveryBatch r.problem r.target r.solution)
      (N volume : ℕ), records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ r.problem.u ≤ r.problem.p ∧
        r.problem.l ≤ cl*r.problem.p ∧ r.problem.wordWidth ≤ cw*r.problem.p ∧
        2^r.problem.l ≤ cr*r.problem.p ∧ r.problem.metadataWidth ≤ cV*r.problem.p ∧
        r.W ≤ cW*r.problem.p ∧ r.problem.rhsExp = 2 ∧ 1 ≤ r.target ∧ r.target ≤ ct*Sizes.p n+1) →
      (∀ r ∈ records, r.problem.metadataWidth ≤ cVratio*r.problem.wordWidth ∧ r.problem.Fs.length = N) →
      (records.map (fun r => replicaRecoveryLocalVolume r.problem)).sum ≤ volume →
      scale*(records.map (fun r => r.runStock hR hQ push c M R K (B r))).sum ≤
        Sizes.T n+C*N*volume*Sizes.p n := by
  let D := 2*(392+cw+cW)+normalizeRecoveryInputPush (Q := Q) (A := A) (U := U)*(4*cW+12*cw+28)+
    completeCachedRecoveryTrafficFactor (A := A) (U := U) hQ R cVratio*cw
  refine ⟨scale*D,?_⟩
  filter_upwards [selectedRawRecoverySharedWorkspaceSchedule_volume_le hR hQ push c M R K cVratio cl cw cr cV cW ct scale]
    with n hshared
  intro h i _ records B N volume hcount hparams hN hvolume
  have hs := hshared h i records B hcount hparams
  have hcost := sum_map_shared_le records
    (fun r => r.runStock hR hQ push c M R K (B r))
    (fun r => rawRecoveryJobSharedWorkspace r (B r) hR hQ push c M R K cVratio)
    (fun r => replicaRecoveryLocalVolume r.problem) (D*N*Sizes.p n) (by
      intro r hr
      obtain ⟨hp,ht,hl,_,_,hw,_,_,hW,_⟩ := hparams r hr
      obtain ⟨hV,hreplicas⟩ := hN r hr
      have hgap : r.problem.t-Sizes.s n i ≤ Sizes.s n i := by
        rw [ht]
        exact selectedAxis_gap_le_source h i
      have hring : r.problem.l = haloInverseRingLog (Sizes.s n i) r.problem.t := by rwa [ht]
      have ha := rawRecoveryJob_runStock_le_affine r (B r) hR hQ push c M R K cVratio hgap hring hV
      have hb := rawRecoveryJobRowWorkspace_local_le (A := A) (U := U) r hQ R cVratio cw cW hw hW
      change rawRecoveryJobRowWorkspace (A := A) (U := U) r hQ R cVratio ≤ D*replicaRecoveryLocalVolume r.problem*r.problem.p at hb
      rw [hreplicas] at ha
      rw [hp] at hb
      nlinarith only [ha,Nat.mul_le_mul_left N hb])
  have hscaled := Nat.mul_le_mul_left scale hcost
  have hv := Nat.mul_le_mul_left (scale*D*N*Sizes.p n) hvolume
  nlinarith only [hs,hscaled,hv]

/-- Restoring every private bank has the same local-volume stock bill. -/
theorem selectedRawRecoveryCleanup_sum_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ)
    (c M R K cVratio cl cw cr cV cW ct scale : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List (RawRecoveryJob (Sizes.s n i)))
      (B : ∀ r : RawRecoveryJob (Sizes.s n i), ReplicaRecoveryBatch r.problem r.target r.solution)
      (N volume : ℕ), records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ r.problem.u ≤ r.problem.p ∧
        r.problem.l ≤ cl*r.problem.p ∧ r.problem.wordWidth ≤ cw*r.problem.p ∧
        2^r.problem.l ≤ cr*r.problem.p ∧ r.problem.metadataWidth ≤ cV*r.problem.p ∧
        r.W ≤ cW*r.problem.p ∧ r.problem.rhsExp = 2 ∧ 1 ≤ r.target ∧ r.target ≤ ct*Sizes.p n+1) →
      (∀ r ∈ records, r.problem.metadataWidth ≤ cVratio*r.problem.wordWidth ∧ r.problem.Fs.length = N) →
      (records.map (fun r => replicaRecoveryLocalVolume r.problem)).sum ≤ volume →
      scale*(records.map (fun r => 6*r.runStock hR hQ push c M R K (B r)+2358)).sum ≤
        Sizes.T n+C*N*volume*Sizes.p n := by
  obtain ⟨C,hstock⟩ := selectedRawRecoveryRunStock_sum_le hR hQ push c M R K cVratio cl cw cr cV cW ct (12*scale)
  refine ⟨C,?_⟩
  filter_upwards [hstock,selectedDistinctCoreSetup_volume_le 2358 0 0 (2*scale)] with n hs hc
  intro h i _ records B N volume hcount hparams hN hvolume
  have hstock' := hs h i records B N volume hcount hparams hN hvolume
  have hcontrols := hc i records (fun _ => 2358) hcount (by simp)
  have hcontrols' : (2*scale)*(2358*records.length) ≤ Sizes.T n := by
    simpa only [List.map_const',List.sum_replicate,smul_eq_mul,Nat.mul_comm] using hcontrols
  have heq (xs : List (RawRecoveryJob (Sizes.s n i))) :
      (xs.map (fun r => 6*r.runStock hR hQ push c M R K (B r)+2358)).sum =
      6*(xs.map (fun r => r.runStock hR hQ push c M R K (B r))).sum+2358*xs.length := by
    induction xs with
    | nil => simp
    | cons r xs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      rw [ih]
      ring
  rw [heq]
  nlinarith only [hstock',hcontrols',Nat.zero_le (C*N*volume*Sizes.p n)]

end IntegerMultBounds.MathlibTM2.Cost
