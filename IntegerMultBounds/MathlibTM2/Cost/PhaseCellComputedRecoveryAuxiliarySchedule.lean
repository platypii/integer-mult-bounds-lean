module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellComputedRecoveryMasterSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoveryDescriptorTraffic

/-! Combine actual fixed setup, shared input stock and local traffic before
applying a fast raw budget. No whole-axis reserve is replicated per core. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {U : Type}

theorem computedCoreMovementScheduleTime_le (V N : ℕ) (records : List (PackedNormalizedJob A s))
    (hN : ∀ r ∈ records, r.Fs.length = N) :
    (records.map (computedCoreMovementTime V)).sum ≤
      records.length*(19*V+14*s+68)+35*(records.map (fun r => (r.b-r.a)*r.W)).sum+
      N*(41*(records.map (fun r => (r.b-r.a)*r.W)).sum+35*records.length) := by
  induction records with
  | nil => simp
  | cons r records ih =>
    have ht := ih (by intro x hx; exact hN x (by simp [hx]))
    have hW : 1 ≤ r.W := by have := r.hW; omega
    have hr := computedCoreMovementTime_le V r N (r.b-r.a) r.W (coreLength s r.coreWidth r.k)
      (hN r (by simp)) rfl rfl rfl hW
    have hL : coreLength s r.coreWidth r.k ≤ r.b-r.a := by have := r.haloLength; omega
    have hvol := Nat.mul_le_mul_right r.W hL
    have hrep := Nat.mul_le_mul_left (N+1) (Nat.add_le_add_right hvol 1)
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [ht,hr,hrep]

theorem selectedComputedAuxiliaryScheduleTime_le (cZ cl cw cV cW : ℕ) (hcZ : 1 ≤ cZ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      {T : ℕ} (work : Fin 392 → Fin T) (records : List (PackedNormalizedJob A (Sizes.s n i))) (N : ℕ),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.t = Sizes.t n i ∧ r.Bcore ≤ cZ*Sizes.p n ∧ r.p ≤ cZ*Sizes.p n ∧
        r.u ≤ cZ*Sizes.p n ∧ r.l ≤ cZ*Sizes.p n ∧ r.targetOut ≤ cZ*Sizes.p n ∧
        r.W ≤ cZ*Sizes.p n ∧ PhaseCellBand.width r.p r.u ≤ cZ*Sizes.p n ∧ 2*r.q+8 ≤ cZ*Sizes.p n) →
      (∀ r ∈ records, r.rawRecoveryJob.problem.p = Sizes.p n ∧ r.rawRecoveryJob.problem.t = Sizes.t n i ∧
        r.rawRecoveryJob.problem.l ≤ cl*r.rawRecoveryJob.problem.p ∧
        r.rawRecoveryJob.problem.wordWidth ≤ cw*r.rawRecoveryJob.problem.p ∧
        r.rawRecoveryJob.problem.metadataWidth ≤ cV*r.rawRecoveryJob.problem.p ∧
        r.rawRecoveryJob.problem.u ≤ r.rawRecoveryJob.problem.p ∧ r.rawRecoveryJob.W ≤ cW*r.rawRecoveryJob.problem.p) →
      (∀ r ∈ records, r.Fs.length = N) →
      (records.map (computedRecoveryAuxiliaryTime work)).sum ≤ Sizes.T n+
        17*(records.map (fun r => (r.b-r.a)*r.W)).sum+8676*records.length+
        N*(340*(records.map (fun r => (r.b-r.a)*r.W)).sum+34589*records.length) := by
  filter_upwards [selectedRecoveryBaseSetup_volume_le cZ 2 hcZ,
    selectedRawRecoverySharedInputStockSchedule_volume_le cl cw cV cW 88] with n hb hs
  intro h i _ T work records N hcount hbase hraw hN
  have hbaseBound := hb h i records hcount hbase
  have hstockBound := hs i (records.map PackedNormalizedJob.rawRecoveryJob)
    (by simpa only [List.length_map] using hcount)
    (by intro r hr; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr; exact hraw x hx)
  simp only [List.map_map,Function.comp_def] at hstockBound
  have haux := computedRecoveryAuxiliaryScheduleTime_le_preparation work records N hN
  simp only [List.sum_map_add,List.sum_map_mul_left] at haux hbaseBound
  nlinarith only [haux,hbaseBound,hstockBound]

/-- Join all actual core costs with one raw schedule and one shared auxiliary
setup allowance. Remaining traffic is linear in total encoded halo volume. -/
theorem computedCoreScheduleTime_le_complete (plan : ComputedRecoveryPlan T)
    (b : RawRecoveryProgramBounds Q A U) (V N setup : ℕ) (records : List (PackedNormalizedJob A s))
    (hN : ∀ r ∈ records, r.Fs.length = N)
    (haux : (records.map (computedRecoveryAuxiliaryTime plan.work)).sum ≤ setup+
      17*(records.map (fun r => (r.b-r.a)*r.W)).sum+8676*records.length+
      N*(340*(records.map (fun r => (r.b-r.a)*r.W)).sum+34589*records.length)) :
    (records.map (plan.coreTimeCost b V)).sum ≤
      rawRecoveryScheduleTimeBudget b plan.work (records.map PackedNormalizedJob.rawRecoveryJob)+setup+
      52*(records.map (fun r => (r.b-r.a)*r.W)).sum+records.length*(19*V+14*s+8754)+
      N*(381*(records.map (fun r => (r.b-r.a)*r.W)).sum+34624*records.length) := by
  have hmovement := computedCoreMovementScheduleTime_le V N records hN
  have heq := computedCoreScheduleTime_eq plan b V records
  simp only [List.sum_map_add] at heq
  nlinarith only [heq,haux,hmovement]

end IntegerMultBounds.MathlibTM2.Cost
