module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoveryScheduleStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryProgramBounds

/-! Storage and cleanup use local coordinates, independently of sparse
numerical boundary work. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedRawRecoveryCoordinateStockBudget_sum_le (b : RawRecoveryProgramBounds Q A U)
    (cVratio cl cw cr cV cW ct scale : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (_v : HS 392 Q A U)
      (records : List (RawRecoveryJob (Sizes.s n i)))
      (N volume : ℕ), records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ r.problem.u ≤ r.problem.p ∧
        r.problem.l ≤ cl*r.problem.p ∧ r.problem.wordWidth ≤ cw*r.problem.p ∧
        2^r.problem.l ≤ cr*r.problem.p ∧ r.problem.metadataWidth ≤ cV*r.problem.p ∧
        r.W ≤ cW*r.problem.p ∧ r.problem.rhsExp = 2 ∧ 1 ≤ r.target ∧ r.target ≤ ct*Sizes.p n+1) →
      (∀ r ∈ records, r.problem.metadataWidth ≤ cVratio*r.problem.wordWidth ∧ r.problem.Fs.length = N) →
      (records.map (fun r => replicaHaloLocalCoordinates r.problem)).sum ≤ volume →
      scale*(records.map (fun r => b.stock r)).sum ≤
        Sizes.T n+C*N*volume*Sizes.p n := by
  let D := 2*(392+cw+cW)+normalizeRecoveryInputPush (Q := Q) (A := A) (U := U)*(4*cW+12*cw+28)+
    completeCachedRecoveryTrafficFactor (A := A) (U := U) b.hQ b.R cVratio*cw
  refine ⟨scale*D,?_⟩
  filter_upwards [selectedRawRecoverySharedWorkspaceSchedule_volume_le b.hR b.hQ b.push b.c b.M b.R b.K
    cVratio cl cw cr cV cW ct scale] with n hshared
  intro h i _ v records N volume hcount hparams hN hvolume
  let B := fun r : RawRecoveryJob (Sizes.s n i) => Classical.choice (b.batch_nonempty v r)
  have hs := hshared h i records B hcount hparams
  have hcost : (records.map b.stock).sum ≤
      (records.map (fun r => rawRecoveryJobSharedWorkspace r (B r) b.hR b.hQ b.push b.c b.M b.R b.K cVratio+
        (D*N*Sizes.p n)*replicaHaloLocalCoordinates r.problem)).sum := by
    apply List.sum_le_sum
    intro r hr
    obtain ⟨hp,ht,hl,_,_,hw,_,_,hW,_⟩ := hparams r hr
    obtain ⟨hV,hreplicas⟩ := hN r hr
    have hgap : r.problem.t-Sizes.s n i ≤ Sizes.s n i := by rw [ht]; exact selectedAxis_gap_le_source h i
    have hring : r.problem.l = haloInverseRingLog (Sizes.s n i) r.problem.t := by rwa [ht]
    have ha := rawRecoveryJob_runStock_le_affine r (B r) b.hR b.hQ b.push b.c b.M b.R b.K cVratio hgap hring hV
    rw [RawRecoveryJob.runStock_eq_budget] at ha
    change b.stock r ≤ _ at ha
    have hb := rawRecoveryJobRowWorkspace_coordinates_le (A := A) (U := U) r b.hQ b.R cVratio cw cW hw hW
    change rawRecoveryJobRowWorkspace (A := A) (U := U) r b.hQ b.R cVratio ≤ D*replicaHaloLocalCoordinates r.problem*r.problem.p at hb
    rw [hreplicas] at ha
    rw [hp] at hb
    nlinarith only [ha,Nat.mul_le_mul_left N hb]
  rw [List.sum_map_add,List.sum_map_mul_left] at hcost
  have hscaled := Nat.mul_le_mul_left scale hcost
  have hv := Nat.mul_le_mul_left (scale*D*N*Sizes.p n) hvolume
  nlinarith only [hs,hscaled,hv]

theorem selectedRawRecoveryCoordinateCleanupBudget_sum_le (b : RawRecoveryProgramBounds Q A U)
    (cVratio cl cw cr cV cW ct scale : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (_v : HS 392 Q A U)
      (records : List (RawRecoveryJob (Sizes.s n i)))
      (N volume : ℕ), records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ r.problem.u ≤ r.problem.p ∧
        r.problem.l ≤ cl*r.problem.p ∧ r.problem.wordWidth ≤ cw*r.problem.p ∧
        2^r.problem.l ≤ cr*r.problem.p ∧ r.problem.metadataWidth ≤ cV*r.problem.p ∧
        r.W ≤ cW*r.problem.p ∧ r.problem.rhsExp = 2 ∧ 1 ≤ r.target ∧ r.target ≤ ct*Sizes.p n+1) →
      (∀ r ∈ records, r.problem.metadataWidth ≤ cVratio*r.problem.wordWidth ∧ r.problem.Fs.length = N) →
      (records.map (fun r => replicaHaloLocalCoordinates r.problem)).sum ≤ volume →
      scale*(records.map (fun r => 6*b.stock r+2358)).sum ≤
        Sizes.T n+C*N*volume*Sizes.p n := by
  obtain ⟨C,hstock⟩ := selectedRawRecoveryCoordinateStockBudget_sum_le b cVratio cl cw cr cV cW ct (12*scale)
  refine ⟨C,?_⟩
  filter_upwards [hstock,selectedDistinctCoreSetup_volume_le 2358 0 0 (2*scale)] with n hs hc
  intro h i _ v records N volume hcount hparams hN hvolume
  have hstock' := hs h i v records N volume hcount hparams hN hvolume
  have hcontrols := hc i records (fun _ => 2358) hcount (by simp)
  have hcontrols' : (2*scale)*(2358*records.length) ≤ Sizes.T n := by
    simpa only [List.map_const',List.sum_replicate,smul_eq_mul,Nat.mul_comm] using hcontrols
  have heq (xs : List (RawRecoveryJob (Sizes.s n i))) :
      (xs.map (fun r => 6*b.stock r+2358)).sum =
      6*(xs.map (fun r => b.stock r)).sum+2358*xs.length := by
    induction xs with
    | nil => simp
    | cons r xs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      rw [ih]
      ring
  rw [heq]
  nlinarith only [hstock',hcontrols',Nat.zero_le (C*N*volume*Sizes.p n)]

end IntegerMultBounds.MathlibTM2.Cost
