module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoveryScheduleTime
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoveryScheduleStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryProgramBounds

/-! Quantitative estimates for the witness-independent scheduler budgets. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedRawRecoveryTimeBudget_sum_le (b : RawRecoveryProgramBounds Q A U)
    (ct cH cW : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n)
      (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (_v : HS 392 Q A U)
      (records : List (RawRecoveryJob (Sizes.s n i)))
      (N band : ℕ),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧
        r.problem.u ≤ Sizes.p n ∧ r.problem.target ≤ cH*Sizes.p n ∧
        r.problem.rhsExp = 2 ∧ r.problem.Fs.length = N ∧
        1 ≤ r.target ∧ r.target ≤ ct*Sizes.p n+1 ∧ r.W ≤ cW*Sizes.p n) →
      (records.map (fun r => r.problem.span)).sum ≤ 9*Sizes.s n i →
      (records.map (fun r => replicaRecoveryLocalVolume r.problem)).sum ≤ 600*(Sizes.s n i+(Sizes.t n i-Sizes.s n i)*band^2) →
      (((records.map RawRecoveryJob.timeBudget).sum : ℕ) : ℝ) ≤
        Sizes.T n+F*N*(Sizes.t n i : ℝ)*(1+(band : ℝ)^2/Sizes.d n)*
          (Sizes.p n : ℝ)^(129/128 : ℝ) := by
  obtain ⟨F,hF,hbound⟩ := selectedRawRecoverySchedule_density_time_le ct cH cW
  refine ⟨F,hF,?_⟩
  filter_upwards [hbound] with n hb
  intro h i _ v records N band hcount hparams hspan hvolume
  let B := fun r : RawRecoveryJob (Sizes.s n i) => Classical.choice (b.batch_nonempty v r)
  have hs := hb h i records B N band hcount hparams hspan hvolume
  simpa only [RawRecoveryJob.runTime_eq_budget] using hs

theorem selectedRawRecoveryStockBudget_sum_le (b : RawRecoveryProgramBounds Q A U) (v : HS 392 Q A U)
    (cVratio cl cw cr cV cW ct scale : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List (RawRecoveryJob (Sizes.s n i)))
      (N volume : ℕ), records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ r.problem.u ≤ r.problem.p ∧
        r.problem.l ≤ cl*r.problem.p ∧ r.problem.wordWidth ≤ cw*r.problem.p ∧
        2^r.problem.l ≤ cr*r.problem.p ∧ r.problem.metadataWidth ≤ cV*r.problem.p ∧
        r.W ≤ cW*r.problem.p ∧ r.problem.rhsExp = 2 ∧ 1 ≤ r.target ∧ r.target ≤ ct*Sizes.p n+1) →
      (∀ r ∈ records, r.problem.metadataWidth ≤ cVratio*r.problem.wordWidth ∧ r.problem.Fs.length = N) →
      (records.map (fun r => replicaRecoveryLocalVolume r.problem)).sum ≤ volume →
      scale*(records.map (fun r => b.stock r)).sum ≤
        Sizes.T n+C*N*volume*Sizes.p n := by
  obtain ⟨C,hbound⟩ := selectedRawRecoveryRunStock_sum_le b.hR b.hQ b.push b.c b.M b.R b.K cVratio cl cw cr cV cW ct scale
  refine ⟨C,?_⟩
  filter_upwards [hbound] with n hb
  intro h i _ records N volume hcount hparams hN hvolume
  let B := fun r : RawRecoveryJob (Sizes.s n i) => Classical.choice (b.batch_nonempty v r)
  have hs := hb h i records B N volume hcount hparams hN hvolume
  simpa only [RawRecoveryJob.runStock_eq_budget,RawRecoveryProgramBounds.stock] using hs

theorem selectedRawRecoveryCleanupBudget_sum_le (b : RawRecoveryProgramBounds Q A U) (v : HS 392 Q A U)
    (cVratio cl cw cr cV cW ct scale : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List (RawRecoveryJob (Sizes.s n i)))
      (N volume : ℕ), records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ r.problem.u ≤ r.problem.p ∧
        r.problem.l ≤ cl*r.problem.p ∧ r.problem.wordWidth ≤ cw*r.problem.p ∧
        2^r.problem.l ≤ cr*r.problem.p ∧ r.problem.metadataWidth ≤ cV*r.problem.p ∧
        r.W ≤ cW*r.problem.p ∧ r.problem.rhsExp = 2 ∧ 1 ≤ r.target ∧ r.target ≤ ct*Sizes.p n+1) →
      (∀ r ∈ records, r.problem.metadataWidth ≤ cVratio*r.problem.wordWidth ∧ r.problem.Fs.length = N) →
      (records.map (fun r => replicaRecoveryLocalVolume r.problem)).sum ≤ volume →
      scale*(records.map (fun r => 6*b.stock r+2358)).sum ≤
        Sizes.T n+C*N*volume*Sizes.p n := by
  obtain ⟨C,hbound⟩ := selectedRawRecoveryCleanup_sum_le b.hR b.hQ b.push b.c b.M b.R b.K cVratio cl cw cr cV cW ct scale
  refine ⟨C,?_⟩
  filter_upwards [hbound] with n hb
  intro h i _ records N volume hcount hparams hN hvolume
  let B := fun r : RawRecoveryJob (Sizes.s n i) => Classical.choice (b.batch_nonempty v r)
  have hs := hb h i records B N volume hcount hparams hN hvolume
  simpa only [RawRecoveryJob.runStock_eq_budget,RawRecoveryProgramBounds.stock] using hs

end IntegerMultBounds.MathlibTM2.Cost
