module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreClassRawRecoveryProfile
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRawRecoveryScheduleFastExec

/-! Actual ordered core jobs execute with fast time and linear space. Only
mathematical halo bounds and physical source/readiness remain as premises. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem selectedCoreClassRawRecovery_fast_exec_within (b : RawRecoveryProgramBounds Q A U)
    (ct : ℕ) :
    ∃ Cspace : ℕ, ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (u target width L : ℕ)
    (hu : u ≤ Sizes.p n) (htarget : target ≤ ct*Sizes.p n)
    (hw : 0 < width) (hwidth : width ≤ Sizes.s n i)
    (hguard : localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u ≤ width)
    (hcell : Sizes.s n i/(Sizes.t n i-Sizes.s n i)+1 ≤ width)
    (hprepare : (Sizes.p n)^2+(PhaseCellBand.width (Sizes.p n) u)^2 ≤ width)
    (α gap : ℝ) (C : ZMod (Sizes.s n i) → GaussianInt)
    (V : Fin (coreGatherIndices (Sizes.s n i) width
      (localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u) L).length → ℕ)
    (bounds : ∀ j, let k := (coreGatherIndices (Sizes.s n i) width
        (localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u) L)[j.val]
      PackedHaloParameterBounds (p := Sizes.p n)
        (l := haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (t := Sizes.t n i)
        (u := u) (target := target+1) (rhsExp := 2)
        (a := (coreHaloEndpoints (Sizes.s n i) width k (PhaseCellBand.width (Sizes.p n) u)
          (localityDepth (Sizes.p n) target)).1)
        (b := (coreHaloEndpoints (Sizes.s n i) width k (PhaseCellBand.width (Sizes.p n) u)
          (localityDepth (Sizes.p n) target)).2) (V := V j) α gap C)
    (Fs : List (ZMod (Sizes.s n i) → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ j, ‖value (Sizes.p n) (F j)‖ ≤ 1),
    let W := packedHaloCommonWidth (Sizes.p n)
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) u (target+1) 2
    let jobs := fun j => RawRecoveryJob.ofComplexBounds (bounds j) Fs hF W
      (packedHaloCommonWidth_fits _ _ _ _ _ _ _ _ _)
    let records := List.ofFn jobs
    ∀ (work : Fin 392 → Fin T) (_hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (_hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (_hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (_hblank : ∀ i, S.R (work i) = []) (_hleft : ∀ i, S.L (work i) = [])
    (_hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (_hsource : S.R src = descriptorScheduleTape work (RawRecoveryJob.words (A := A)) records++rest)
    (_hclock : (S.R clock).length = records.length) (_hsaved : S.R saved = []) (_hsavedClock : S.R savedClock = []),
    let step := normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A) work src saved count tmp spare result b.hR b.hQ
    ∃ v', ∃ steps : ℕ, ∃ outputs, v'.user = v.user ∧
      (steps : ℝ) ≤ 4*Sizes.T n+F*(2*Fs.length)*(Sizes.t n i : ℝ)*(1+(PhaseCellBand.width (Sizes.p n) u : ℝ)^2/Sizes.d n)*
        (Sizes.p n : ℝ)^(129/128 : ℝ) ∧
      Exec body (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) steps
        (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) ∧
      List.Forall₂ RawRecoveryJob.output records outputs ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule src saved tmp clock savedClock step) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (Cprog+1)*(3*Sizes.T n+Cspace*(2*Fs.length)*Sizes.s n i*Sizes.p n)) depth
          (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) steps
          (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) := by
  let cH := 1032+8*ct
  let cw := 16*20+8*cH+8*2+128
  let cVratio := 2*cw+426009
  obtain ⟨Cspace,F,hF,hbound⟩ := selectedRawRecoverySchedule_fast_exec_within
    (body := body) b cVratio 20 cw 20 (cVratio*cw) cH ct cH
  refine ⟨Cspace,F,hF,?_⟩
  filter_upwards [hbound] with n hs
  intro h i _ u target width L hu htarget hw hwidth hguard hcell hprepare α gap C V bounds Fs hFs
  dsimp only
  intro work hwork src saved count tmp spare result clock savedClock hreg hsep
    v S rest hblank hleft hscratch hsource hclock hsaved hsavedClock
  let W := packedHaloCommonWidth (Sizes.p n)
    (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) u (target+1) 2
  let jobs := fun j => RawRecoveryJob.ofComplexBounds (bounds j) Fs hFs W
    (packedHaloCommonWidth_fits _ _ _ _ _ _ _ _ _)
  obtain ⟨hcount,hparams,hN,hcoordinates,hspan,hH,hvolume⟩ :=
    selectedCoreClassRawRecovery_profile ct h i u target width L hu htarget hw hwidth hguard
      hcell hprepare α gap C V bounds Fs hFs
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hs h i work hwork src saved count tmp spare result clock savedClock hreg hsep
    (List.ofFn jobs) (2*Fs.length) (PhaseCellBand.width (Sizes.p n) u)
    hcount hparams hN hcoordinates hspan hH hvolume v S rest
    hblank hleft hscratch hsource hclock hsaved hsavedClock

end IntegerMultBounds.MathlibTM2.Cost
