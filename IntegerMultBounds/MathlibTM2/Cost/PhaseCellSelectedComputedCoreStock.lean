module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellComputedCoreTraffic
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRawRecoverySingletonWorkspace

/-! Complete computed-core stock has linear precision and coordinate volume.
The actual time exponent and sparse numerical density do not enter this bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedComputedCoreStock_sum_le (b : RawRecoveryProgramBounds Q A U)
    (cZ cScalar cVratio cl cw cr cV cW ct : ℕ) (hcZ : 1 ≤ cZ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (_v : HS 392 Q A U)
      {T : ℕ} (plan : ComputedRecoveryPlan T) (V : ℕ) (records : List (PackedNormalizedJob A (Sizes.s n i)))
      (N Cprog : ℕ), records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.rawRecoveryJob.problem.p = Sizes.p n ∧ r.rawRecoveryJob.problem.t = Sizes.t n i ∧
        r.rawRecoveryJob.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ r.rawRecoveryJob.problem.u ≤ r.rawRecoveryJob.problem.p ∧
        r.rawRecoveryJob.problem.l ≤ cl*r.rawRecoveryJob.problem.p ∧ r.rawRecoveryJob.problem.wordWidth ≤ cw*r.rawRecoveryJob.problem.p ∧
        2^r.rawRecoveryJob.problem.l ≤ cr*r.rawRecoveryJob.problem.p ∧ r.rawRecoveryJob.problem.metadataWidth ≤ cV*r.rawRecoveryJob.problem.p ∧
        r.rawRecoveryJob.W ≤ cW*r.rawRecoveryJob.problem.p ∧ r.rawRecoveryJob.problem.rhsExp = 2 ∧ 1 ≤ r.rawRecoveryJob.target ∧ r.rawRecoveryJob.target ≤ ct*Sizes.p n+1) →
      (∀ r ∈ records, r.rawRecoveryJob.problem.metadataWidth ≤ cVratio*r.rawRecoveryJob.problem.wordWidth ∧ r.rawRecoveryJob.problem.Fs.length = 2*N) →
      (records.map (fun r => replicaHaloLocalCoordinates r.rawRecoveryJob.problem)).sum ≤ 163*Sizes.s n i →
      (records.map (fun r => r.rawRecoveryJob.problem.span)).sum ≤ 9*Sizes.s n i →
      (∀ r ∈ records, r.t = Sizes.t n i ∧ r.Bcore ≤ cZ*Sizes.p n ∧ r.p ≤ cZ*Sizes.p n ∧
        r.u ≤ cZ*Sizes.p n ∧ r.l ≤ cZ*Sizes.p n ∧ r.targetOut ≤ cZ*Sizes.p n ∧
        r.W ≤ cZ*Sizes.p n ∧ PhaseCellBand.width r.p r.u ≤ cZ*Sizes.p n ∧ 2*r.q+8 ≤ cZ*Sizes.p n) →
      V ≤ cScalar*Sizes.p n → (∀ r ∈ records, r.Fs.length = N) →
      (records.map (fun r => plan.coreStock b V r Cprog)).sum ≤
        (39+3*Cprog)*Sizes.T n+C*(Cprog+1)*N*Sizes.t n i*Sizes.p n := by
  obtain ⟨Cr,hraw⟩ := selectedRawRecoverySingletonWorkspaceBudgets_sum_le b cVratio cl cw cr cV cW ct
  let Ct := 3429*cW+69248
  refine ⟨18*Ct+2*Cr,?_⟩
  filter_upwards [hraw,selectedComputedAuxiliaryScheduleTime_le cZ cl cw cV cW hcZ,
    selectedAxisPolynomial_le_volume (468*cW+38*cScalar+17536) 1 2] with n hn ha hpoly
  intro h i _ v T plan V records N Cprog hcount hparams hN hcoordinates hspan hsetup hV hFs
  have hrawBound := hn h i v plan.work (records.map PackedNormalizedJob.rawRecoveryJob) (2*N)
    (by simpa only [List.length_map] using hcount)
    (by intro r hr; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr; exact hparams x hx)
    (by intro r hr; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr; exact hN x hx)
    (by simpa only [List.map_map,Function.comp_def] using hcoordinates)
    (by simpa only [List.map_map,Function.comp_def] using hspan)
  simp only [List.map_map,Function.comp_def] at hrawBound
  have haux := ha h i plan.work records N hcount hsetup (by
    intro r hr
    obtain ⟨hp,ht,_,hu,hl,hw,_,hmeta,hW,_⟩ := hparams r hr
    exact ⟨hp,ht,hl,hw,hmeta,hu,hW⟩) hFs
  let D := (records.map (fun r => (r.b-r.a)*r.W)).sum
  have hD : D ≤ 9*cW*Sizes.s n i*Sizes.p n := by
    calc
      D ≤ (records.map (fun r => r.rawRecoveryJob.problem.span*(cW*Sizes.p n))).sum := by
        apply List.sum_le_sum
        intro r hr
        obtain ⟨hp,_,_,_,_,_,_,_,hW,_⟩ := hparams r hr
        have hw : r.W ≤ cW*Sizes.p n := by
          simpa only [r.rawRecoveryJob_profile.2.2.2.2.1,hp] using hW
        rw [←r.rawRecoveryJob_profile.2.2.1]
        exact Nat.mul_le_mul_left _ hw
      _ = (records.map (fun r => r.rawRecoveryJob.problem.span)).sum*(cW*Sizes.p n) := List.sum_map_mul_right _ _ _
      _ ≤ (9*Sizes.s n i)*(cW*Sizes.p n) := Nat.mul_le_mul_right _ hspan
      _ = _ := by ring
  have hp1 : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have htraffic := computedCoreTraffic_le cScalar cW (Sizes.p n) (Sizes.s n i) (Sizes.t n i) V records.length D
    hp1 (Nat.le_of_lt (h.good.lt i)) hV hcount hD
  have hcontrol : 52*D+records.length*(19*V+14*Sizes.s n i+8754) ≤ Sizes.T n :=
    htraffic.1.trans (by simpa only [pow_one] using hpoly i)
  have hmovement := computedCoreMovementScheduleTime_le V N records hFs
  have hauxMovement : (records.map (fun r => computedRecoveryAuxiliaryTime plan.work r+
      computedCoreMovementTime V r)).sum ≤ 2*Sizes.T n+Ct*N*Sizes.t n i*Sizes.p n := by
    rw [List.sum_map_add]
    have hrow := Nat.mul_le_mul_left N htraffic.2
    dsimp only [D,Ct] at hcontrol hrow ⊢
    nlinarith only [haux,hmovement,hcontrol,hrow]
  have hstock := computedCoreStock_sum_le plan b V Cprog records
  have hst : Sizes.s n i ≤ Sizes.t n i := Nat.le_of_lt (h.good.lt i)
  have hrawLinear : (records.map (fun r => rawRecoveryScheduleWorkspaceBudget b plan.work [r.rawRecoveryJob])).sum ≤
      3*Sizes.T n+2*Cr*N*Sizes.t n i*Sizes.p n := by
    have hmul := Nat.mul_le_mul_left (2*Cr*N) hst
    nlinarith only [hrawBound,Nat.mul_le_mul_right (Sizes.p n) hmul]
  have hscaledAux := Nat.mul_le_mul_left 18 hauxMovement
  have hscaledRaw := Nat.mul_le_mul_left (Cprog+1) hrawLinear
  have hpad : 18*Ct*N*Sizes.t n i*Sizes.p n ≤
      18*Ct*(Cprog+1)*N*Sizes.t n i*Sizes.p n := by
    have hh := Nat.mul_le_mul_left (18*Ct*N*Sizes.t n i*Sizes.p n)
      (show 1 ≤ Cprog+1 by omega)
    nlinarith only [hh]
  nlinarith only [hstock,hscaledAux,hscaledRaw,hpad]

end IntegerMultBounds.MathlibTM2.Cost
