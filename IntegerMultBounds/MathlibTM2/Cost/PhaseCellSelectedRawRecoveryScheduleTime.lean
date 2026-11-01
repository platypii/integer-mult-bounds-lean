module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRawRecoveryScheduleWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoveryScheduleBudgetCosts

/-! The actual restoring scheduler pays one fast numerical bill and fixed
shared reserves, including descriptor traffic and cleanup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedRawRecoveryScheduleTimeBudget_le (b : RawRecoveryProgramBounds Q A U)
    (cVratio cl cw cr cV cW ct cH : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (_v : HS 392 Q A U)
      {T : ℕ} (work : Fin 392 → Fin T) (records : List (RawRecoveryJob (Sizes.s n i)))
      (N band : ℕ), records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ r.problem.u ≤ r.problem.p ∧
        r.problem.l ≤ cl*r.problem.p ∧ r.problem.wordWidth ≤ cw*r.problem.p ∧
        2^r.problem.l ≤ cr*r.problem.p ∧ r.problem.metadataWidth ≤ cV*r.problem.p ∧
        r.W ≤ cW*r.problem.p ∧ r.problem.rhsExp = 2 ∧ 1 ≤ r.target ∧ r.target ≤ ct*Sizes.p n+1) →
      (∀ r ∈ records, r.problem.metadataWidth ≤ cVratio*r.problem.wordWidth ∧ r.problem.Fs.length = N) →
      (records.map (fun r => replicaHaloLocalCoordinates r.problem)).sum ≤ 163*Sizes.s n i →
      (records.map (fun r => r.problem.span)).sum ≤ 9*Sizes.s n i →
      (∀ r ∈ records, r.problem.target ≤ cH*Sizes.p n) →
      (records.map (fun r => replicaRecoveryLocalVolume r.problem)).sum ≤
        600*(Sizes.s n i+(Sizes.t n i-Sizes.s n i)*band^2) →
      (rawRecoveryScheduleTimeBudget b work records : ℝ) ≤
        4*Sizes.T n+F*N*(Sizes.t n i : ℝ)*(1+(band : ℝ)^2/Sizes.d n)*(Sizes.p n : ℝ)^(129/128 : ℝ) := by
  obtain ⟨F,hF,htime⟩ := selectedRawRecoveryTimeBudget_sum_le b ct cH cW
  obtain ⟨Cc,hcleanup⟩ := selectedRawRecoveryCoordinateCleanupBudget_sum_le b cVratio cl cw cr cV cW ct 1
  let Cd := 42336+243*(cw+cW)
  let D := 163*Cc+Cd
  refine ⟨F+D,by positivity,?_⟩
  filter_upwards [htime,hcleanup,selectedRawRecoveryDescriptorTraffic_le cl cw cV cW,
    selectedAxisPolynomial_le_volume 16 1 1] with n ht hc hd hsmall
  intro h i _ v T work records N band hcount hparams hN hcoordinates hspan htarget hvolume
  have hcaller := ht h i v records N band hcount (by
    intro r hr
    obtain ⟨hp,ht,hl,hu,_,_,_,_,hW,he,hpos,htarget'⟩ := hparams r hr
    exact ⟨hp,ht,hl,by simpa only [hp] using hu,htarget r hr,he,(hN r hr).2,hpos,htarget',
      by simpa only [hp] using hW⟩) hspan hvolume
  have hclean := hc h i v records N (163*Sizes.s n i) hcount hparams hN hcoordinates
  simp only [one_mul] at hclean
  have hdesc := hd i (A := A) work records N (9*Sizes.s n i) hcount (by
    intro r hr
    obtain ⟨hp,ht,_,hu,hl,hw,_,hV,hW,_⟩ := hparams r hr
    exact ⟨hp,ht,hl,hw,hV,hu,hW⟩) (by intro r hr; exact (hN r hr).2) hspan
  have hp1 : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have ht1 : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have htsp := Nat.le_mul_of_pos_right (Sizes.t n i) hp1
  have htp : 1 ≤ Sizes.t n i*Sizes.p n := Nat.mul_pos ht1 hp1
  have hcontrol : 3*records.length+10 ≤ Sizes.T n := by
    have hh := hsmall i
    simp only [pow_one] at hh
    nlinarith only [hcount,htsp,htp,hh]
  have hgap := selectedAxis_gap_le_source h i
  have hst := h.good.lt i
  have hcountS : records.length ≤ 4*Sizes.s n i := by omega
  have hsp := Nat.le_mul_of_pos_right (Sizes.s n i) hp1
  have hncontrol : 392*records.length ≤ 1568*Sizes.s n i*Sizes.p n := by nlinarith only [hcountS,hsp]
  have htraffic : 2*(descriptorScheduleTape work (RawRecoveryJob.words (A := A)) records).length+
      (records.map (fun r => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A))))).sum+
      6*records.length ≤ Sizes.T n+Cd*N*Sizes.s n i*Sizes.p n := by
    have hscaled := Nat.mul_le_mul_left (27*N) hncontrol
    dsimp only [Cd]
    nlinarith only [hdesc,hscaled]
  have hpR : (1 : ℝ) ≤ Sizes.p n := by exact_mod_cast hp1
  have hpPow := Real.self_le_rpow_of_one_le hpR (by norm_num : (1 : ℝ) ≤ 129/128)
  have hsR : (Sizes.s n i : ℝ) ≤ Sizes.t n i := by exact_mod_cast hst.le
  have hnonneg : (0 : ℝ) ≤ (band : ℝ)^2/Sizes.d n := by positivity
  have htR : (Sizes.t n i : ℝ) ≤ (Sizes.t n i : ℝ)*(1+(band : ℝ)^2/Sizes.d n) := by
    nlinarith only [mul_nonneg (Nat.cast_nonneg (Sizes.t n i) : (0 : ℝ) ≤ Sizes.t n i) hnonneg]
  have hlinear := mul_le_mul (hsR.trans htR) hpPow (by positivity)
    (by positivity : (0 : ℝ) ≤ (Sizes.t n i : ℝ)*(1+(band : ℝ)^2/Sizes.d n))
  have hlin := mul_le_mul_of_nonneg_left hlinear (by positivity : (0 : ℝ) ≤ (D : ℝ)*N)
  have hcleanR := (Nat.cast_le (α := ℝ)).mpr hclean
  have htrafficR := (Nat.cast_le (α := ℝ)).mpr htraffic
  have hcontrolR := (Nat.cast_le (α := ℝ)).mpr hcontrol
  have heq := congrArg (fun x : ℕ => (x : ℝ)) (rawRecoveryScheduleTimeBudget_eq b work records)
  change _ ≤ (4 : ℝ)*Sizes.T n+(F+(D : ℝ))*N*(Sizes.t n i : ℝ)*
    (1+(band : ℝ)^2/Sizes.d n)*(Sizes.p n : ℝ)^(129/128 : ℝ)
  dsimp only [D] at hlin ⊢
  push_cast at heq hcaller hcleanR htrafficR hcontrolR hlin ⊢
  nlinarith only [heq,hcaller,hcleanR,htrafficR,hcontrolR,hlin]

end IntegerMultBounds.MathlibTM2.Cost
