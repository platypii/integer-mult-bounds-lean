module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellComputedRecoveryScheduleLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRawRecoveryScheduleTime

/-! Apply the fast raw-schedule bound once to the complete computed class,
leaving every auxiliary and movement bill explicit for grouped absorption. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedComputedCoreScheduleTime_le (b : RawRecoveryProgramBounds Q A U)
    (cVratio cl cw cr cV cW ct cH : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (_v : HS 392 Q A U)
      {T : ℕ} (plan : ComputedRecoveryPlan T) (V : ℕ) (records : List (PackedNormalizedJob A (Sizes.s n i)))
      (N band : ℕ), records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.rawRecoveryJob.problem.p = Sizes.p n ∧ r.rawRecoveryJob.problem.t = Sizes.t n i ∧
        r.rawRecoveryJob.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ r.rawRecoveryJob.problem.u ≤ r.rawRecoveryJob.problem.p ∧
        r.rawRecoveryJob.problem.l ≤ cl*r.rawRecoveryJob.problem.p ∧ r.rawRecoveryJob.problem.wordWidth ≤ cw*r.rawRecoveryJob.problem.p ∧
        2^r.rawRecoveryJob.problem.l ≤ cr*r.rawRecoveryJob.problem.p ∧ r.rawRecoveryJob.problem.metadataWidth ≤ cV*r.rawRecoveryJob.problem.p ∧
        r.rawRecoveryJob.W ≤ cW*r.rawRecoveryJob.problem.p ∧ r.rawRecoveryJob.problem.rhsExp = 2 ∧ 1 ≤ r.rawRecoveryJob.target ∧ r.rawRecoveryJob.target ≤ ct*Sizes.p n+1) →
      (∀ r ∈ records, r.rawRecoveryJob.problem.metadataWidth ≤ cVratio*r.rawRecoveryJob.problem.wordWidth ∧ r.rawRecoveryJob.problem.Fs.length = N) →
      (records.map (fun r => replicaHaloLocalCoordinates r.rawRecoveryJob.problem)).sum ≤ 163*Sizes.s n i →
      (records.map (fun r => r.rawRecoveryJob.problem.span)).sum ≤ 9*Sizes.s n i →
      (∀ r ∈ records, r.rawRecoveryJob.problem.target ≤ cH*Sizes.p n) →
      (records.map (fun r => replicaRecoveryLocalVolume r.rawRecoveryJob.problem)).sum ≤
        600*(Sizes.s n i+(Sizes.t n i-Sizes.s n i)*band^2) →
      (((records.map (plan.coreTimeCost b V)).sum : ℕ) : ℝ) ≤
        4*Sizes.T n+F*N*(Sizes.t n i : ℝ)*(1+(band : ℝ)^2/Sizes.d n)*(Sizes.p n : ℝ)^(129/128 : ℝ)+
        ((records.map (fun r => computedRecoveryAuxiliaryTime plan.work r+computedCoreMovementTime V r)).sum : ℕ)+
        10*records.length := by
  obtain ⟨F,hF,hbound⟩ := selectedRawRecoveryScheduleTimeBudget_le b cVratio cl cw cr cV cW ct cH
  refine ⟨F,hF,?_⟩
  filter_upwards [hbound] with n hn
  intro h i _ v T plan V records N band hcount hparams hN hcoordinates hspan htarget hvolume
  have hraw := hn h i v plan.work (records.map PackedNormalizedJob.rawRecoveryJob) N band
    (by simpa only [List.length_map] using hcount)
    (by intro r hr; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr; exact hparams x hx)
    (by intro r hr; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr; exact hN x hx)
    (by simpa only [List.map_map,Function.comp_def] using hcoordinates)
    (by simpa only [List.map_map,Function.comp_def] using hspan)
    (by intro r hr; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr; exact htarget x hx)
    (by simpa only [List.map_map,Function.comp_def] using hvolume)
  have heq := congrArg (fun k : ℕ => (k : ℝ)) (computedCoreScheduleTime_eq plan b V records)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at heq
  linarith

end IntegerMultBounds.MathlibTM2.Cost
