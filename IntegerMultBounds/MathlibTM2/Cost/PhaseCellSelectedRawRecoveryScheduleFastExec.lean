module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRawRecoveryScheduleExec
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRawRecoveryScheduleTime

/-! The restoring scheduler combines fast numerical time and linear packed-axis space. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem selectedRawRecoverySchedule_fast_exec_within (b : RawRecoveryProgramBounds Q A U)
    (cVratio cl cw cr cV cW ct cH : ℕ) :
    ∃ C : ℕ, ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
    (work : Fin 392 → Fin T) (_hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (_hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (_hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (records : List (RawRecoveryJob (Sizes.s n i))) (N band : ℕ)
    (_hcount : records.length ≤ 2*Sizes.t n i)
    (_hparams : ∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
      r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ r.problem.u ≤ r.problem.p ∧
      r.problem.l ≤ cl*r.problem.p ∧ r.problem.wordWidth ≤ cw*r.problem.p ∧
      2^r.problem.l ≤ cr*r.problem.p ∧ r.problem.metadataWidth ≤ cV*r.problem.p ∧
      r.W ≤ cW*r.problem.p ∧ r.problem.rhsExp = 2 ∧ 1 ≤ r.target ∧ r.target ≤ ct*Sizes.p n+1)
    (_hN : ∀ r ∈ records, r.problem.metadataWidth ≤ cVratio*r.problem.wordWidth ∧ r.problem.Fs.length = N)
    (_hcoordinates : (records.map (fun r => replicaHaloLocalCoordinates r.problem)).sum ≤ 163*Sizes.s n i)
    (_hspan : (records.map (fun r => r.problem.span)).sum ≤ 9*Sizes.s n i)
    (_htarget : ∀ r ∈ records, r.problem.target ≤ cH*Sizes.p n)
    (_hvolume : (records.map (fun r => replicaRecoveryLocalVolume r.problem)).sum ≤
      600*(Sizes.s n i+(Sizes.t n i-Sizes.s n i)*band^2))
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (_hblank : ∀ i, S.R (work i) = []) (_hleft : ∀ i, S.L (work i) = [])
    (_hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (_hsource : S.R src = descriptorScheduleTape work (RawRecoveryJob.words (A := A)) records++rest)
    (_hclock : (S.R clock).length = records.length) (_hsaved : S.R saved = []) (_hsavedClock : S.R savedClock = []),
    let step := normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A) work src saved count tmp spare result b.hR b.hQ
    ∃ v', ∃ steps : ℕ, ∃ outputs, v'.user = v.user ∧
      (steps : ℝ) ≤ 4*Sizes.T n+F*N*(Sizes.t n i : ℝ)*(1+(band : ℝ)^2/Sizes.d n)*
        (Sizes.p n : ℝ)^(129/128 : ℝ) ∧
      Exec body (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) steps
        (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) ∧
      List.Forall₂ RawRecoveryJob.output records outputs ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule src saved tmp clock savedClock step) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (Cprog+1)*(3*Sizes.T n+C*N*Sizes.s n i*Sizes.p n)) depth
          (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) steps
          (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) := by
  obtain ⟨C,hspace⟩ := selectedRawRecoverySchedule_exec_within (body := body) b cVratio cl cw cr cV cW ct
  obtain ⟨F,hF,htime⟩ := selectedRawRecoveryScheduleTimeBudget_le b cVratio cl cw cr cV cW ct cH
  refine ⟨C,F,hF,?_⟩
  filter_upwards [hspace,htime] with n hs ht
  intro h i _ work hwork src saved count tmp spare result clock savedClock hreg hsep records N band
    hcount hparams hN hcoordinates hspan htarget hvolume v S rest hblank hleft hscratch hsource hclock hsaved hsavedClock
  let v₀ : HS 392 Q A U := ⟨false,none,v.st,fun _ => 0,none,v.user⟩
  have hbudget := ht h i v₀ work records N band hcount hparams hN hcoordinates hspan htarget hvolume
  obtain ⟨v',steps,outputs,hu,hn,he,hgood,htrace⟩ := hs h i work hwork src saved count tmp spare result
    clock savedClock hreg hsep records N hcount hparams hN hcoordinates hspan v S rest
    hblank hleft hscratch hsource hclock hsaved hsavedClock
  refine ⟨v',steps,outputs,hu,?_,he,hgood,htrace⟩
  have hsteps : (steps : ℝ) ≤ rawRecoveryScheduleTimeBudget b work records := by exact_mod_cast hn
  exact hsteps.trans hbudget

end IntegerMultBounds.MathlibTM2.Cost
