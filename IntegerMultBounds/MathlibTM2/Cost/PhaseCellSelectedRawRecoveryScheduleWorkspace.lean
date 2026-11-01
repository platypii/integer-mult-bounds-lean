module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreClassRecoveryStorage
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoveryScheduleBudgetCosts

/-! The actual scheduler workspace has linear packed-axis storage, with no
sparse numerical density factor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedRawRecoveryScheduleWorkspaceBudget_le (b : RawRecoveryProgramBounds Q A U)
    (cVratio cl cw cr cV cW ct : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (_v : HS 392 Q A U)
      {T : ℕ} (work : Fin 392 → Fin T) (records : List (RawRecoveryJob (Sizes.s n i)))
      (N : ℕ), records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ r.problem.u ≤ r.problem.p ∧
        r.problem.l ≤ cl*r.problem.p ∧ r.problem.wordWidth ≤ cw*r.problem.p ∧
        2^r.problem.l ≤ cr*r.problem.p ∧ r.problem.metadataWidth ≤ cV*r.problem.p ∧
        r.W ≤ cW*r.problem.p ∧ r.problem.rhsExp = 2 ∧ 1 ≤ r.target ∧ r.target ≤ ct*Sizes.p n+1) →
      (∀ r ∈ records, r.problem.metadataWidth ≤ cVratio*r.problem.wordWidth ∧ r.problem.Fs.length = N) →
      (records.map (fun r => replicaHaloLocalCoordinates r.problem)).sum ≤ 163*Sizes.s n i →
      (records.map (fun r => r.problem.span)).sum ≤ 9*Sizes.s n i →
      rawRecoveryScheduleWorkspaceBudget b work records ≤
        3*Sizes.T n+C*N*Sizes.s n i*Sizes.p n := by
  obtain ⟨Cs,hstock⟩ := selectedRawRecoveryCoordinateStockBudget_sum_le b cVratio cl cw cr cV cW ct 7
  let Cd := 42336+243*(cw+cW)
  refine ⟨163*Cs+Cd+9*cw,?_⟩
  filter_upwards [hstock,selectedRawRecoveryDescriptorTraffic_le cl cw cV cW,
    selectedAxisPolynomial_le_volume 4724 1 1] with n hs hd hsmall
  intro h i _ v T work records N hcount hparams hN hcoordinates hspan
  have hstock' := hs h i v records N (163*Sizes.s n i) hcount hparams hN hcoordinates
  have hdesc := hd i (A := A) work records N (9*Sizes.s n i) hcount (by
    intro r hr
    obtain ⟨hp,ht,_,hu,hl,hw,_,hV,hW,_⟩ := hparams r hr
    exact ⟨hp,ht,hl,hw,hV,hu,hW⟩) (by intro r hr; exact (hN r hr).2) hspan
  have houtput := rawRecoverySchedule_outputVolume_le records N (Sizes.p n) cw (9*Sizes.s n i) (by
    intro r hr
    obtain ⟨hp,_,_,_,_,hw,_⟩ := hparams r hr
    exact ⟨(hN r hr).2,by simpa only [hp] using hw⟩) hspan
  have hp1 : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have ht1 : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have htsp := Nat.le_mul_of_pos_right (Sizes.t n i) hp1
  have htp : 1 ≤ Sizes.t n i*Sizes.p n := Nat.mul_pos ht1 hp1
  have hconstant : 2358*records.length+8 ≤ Sizes.T n := by
    have hh := hsmall i
    simp only [pow_one] at hh
    nlinarith only [hcount,htsp,htp,hh]
  have hgap := selectedAxis_gap_le_source h i
  have hst := h.good.lt i
  have hcountS : records.length ≤ 4*Sizes.s n i := by omega
  have hsp := Nat.le_mul_of_pos_right (Sizes.s n i) hp1
  have hncontrol : 392*records.length ≤ 1568*Sizes.s n i*Sizes.p n := by
    nlinarith only [hcountS,hsp]
  have htraffic : 2*(descriptorScheduleTape work (RawRecoveryJob.words (A := A)) records).length+
      (records.map (fun r => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A))))).sum+
      6*records.length ≤ Sizes.T n+Cd*N*Sizes.s n i*Sizes.p n := by
    have hscaled := Nat.mul_le_mul_left (27*N) hncontrol
    dsimp only [Cd]
    nlinarith only [hdesc,hscaled]
  have hb := rawRecoveryScheduleWorkspaceBudget_le b work records
  change _ ≤ 3*Sizes.T n+(163*Cs+Cd+9*cw)*N*Sizes.s n i*Sizes.p n
  nlinarith only [hb,hstock',htraffic,houtput,hconstant]

end IntegerMultBounds.MathlibTM2.Cost
