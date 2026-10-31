module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedRowSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRowExactInverse

/-! The ordered packed producer carries exact-inverse core accuracy and unit
ball certificates on its actual rows, with unchanged execution and resource bills. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem packedExactRowSchedule_exec
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (work : Fin 325 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (records : List (PackedNormalizedJob A s)) (W : ℕ) (hwidth : ∀ r ∈ records, r.W = W) (v : HS T Q A U) (S : Stacks T A)
    (t : ℕ) [NeZero t] (ht : ∀ r ∈ records, r.t = t)
    (hp : ∀ r ∈ records, 4 ≤ r.p) (htarget : ∀ r ∈ records, r.p+2 ≤ r.targetOut)
    (hlocal : ∀ r ∈ records, r.localityTarget = r.targetOut)
    (J : PackedNormalizedJob A s → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : ∀ r ∈ records, J r ∘L IntegerMultBounds.NLogN.PhaseCellOperator.exact s t r.α = 1)
    (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hsource : S.R src = descriptorScheduleTape work PackedNormalizedJob.words records.reverse++rest)
    (hclock : (S.R clock).length = records.length) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) :
    let step := packedNormalizedDescriptorStep (P := P) (U := U) (A := A) work src saved count tmp spare result hR hQ
    ∃ v' n, ∃ rowBatches : List (List (List GaussianInt)), v'.user = v.user ∧
      n ≤ (records.reverse.map (fun r => takeDescriptorBankCost (placedDescriptorFields work r.words)+
        r.setupTime+r.cleanup (U := U) hR hQ+3)).sum+
        (records.reverse.map (fun r => r.Fs.length*r.replicaTime)).sum+6*records.length+
        2*(descriptorScheduleTape work PackedNormalizedJob.words records.reverse).length+10 ∧
      Exec body (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
        (mk v' {S with R := Function.update S.R result ((rowBatches.map (fun rows => cstream A W rows.flatten)).flatten++S.R result)}) ∧
      List.Forall₂ (fun r rows => r.ExactRowOutput (J r) rows) records rowBatches ∧
      ∀ C, mnProgPush (descriptorSolverSchedule src saved tmp clock savedClock step) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*((records.reverse.map PackedNormalizedJob.outputVolume).sum+(records.reverse.map (fun r => r.stepStock (U := U) work hR hQ)).foldr max 0+6*records.length+
            2*(descriptorScheduleTape work PackedNormalizedJob.words records.reverse).length+8)) depth
          (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
          (mk v' {S with R := Function.update S.R result ((rowBatches.map (fun rows => cstream A W rows.flatten)).flatten++S.R result)}) := by
  dsimp only
  obtain ⟨v',n,rowBatches,hu,hn,he,hrows,hstock⟩ := packedNormalizedRowSchedule_ordered_exec (body := body)
    hR hQ hA work hwork src saved count tmp spare result clock savedClock hreg hsep records W hwidth v S rest
    hblank hleft hscratch hsource hclock hsaved hsavedClock
  refine ⟨v',n,rowBatches,hu,hn,he,?_,hstock⟩
  have hm := (List.forall₂_and_left records rowBatches).mpr ⟨fun _ hr => hr,hrows⟩
  apply hm.imp
  intro r rows hpair
  obtain ⟨hr,hrow⟩ := hpair
  have hteq := ht r hr
  letI : NeZero r.t := ⟨by rw [hteq]; exact NeZero.ne t⟩
  exact hrow.exact_inverse r (hp r hr) (htarget r hr) (hlocal r hr) (J r)
    (by simpa only [hteq] using hJ r hr)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
