module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedExactRowSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreTileRows

/-! The packed producer returns the archive transpose's rectangular row ABI,
with exact bytes, numerical certificates, time and peak-stock guarantees. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem packedExactTileSchedule_exec
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
    (B L : ℕ) (hreplicas : ∀ r ∈ records, r.Fs.length = B)
    (hcore : ∀ r ∈ records, IntegerMultBounds.NLogN.PhaseCellMatrix.coreLength s r.coreWidth r.k = L)
    (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hsource : S.R src = descriptorScheduleTape work PackedNormalizedJob.words records.reverse++rest)
    (hclock : (S.R clock).length = records.length) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) :
    let step := packedNormalizedDescriptorStep (P := P) (U := U) (A := A) work src saved count tmp spare result hR hQ
    ∃ v' n, ∃ tileRows : Fin records.length → Fin B → List GaussianInt, v'.user = v.user ∧
      n ≤ (records.reverse.map (fun r => takeDescriptorBankCost (placedDescriptorFields work r.words)+
        r.setupTime+r.cleanup (U := U) hR hQ+3)).sum+
        (records.reverse.map (fun r => r.Fs.length*r.replicaTime)).sum+6*records.length+
        2*(descriptorScheduleTape work PackedNormalizedJob.words records.reverse).length+10 ∧
      Exec body (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
        (mk v' {S with R := Function.update S.R result ((List.ofFn fun i => (List.ofFn fun j => cstream A W (tileRows i j)).flatten).flatten++S.R result)}) ∧
      (∀ i j, (tileRows i j).length = L) ∧
      (∀ i : Fin records.length, (records.get i).ExactRowOutput (J (records.get i)) (List.ofFn (tileRows i))) ∧
      ∀ C, mnProgPush (descriptorSolverSchedule src saved tmp clock savedClock step) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*((records.reverse.map PackedNormalizedJob.outputVolume).sum+(records.reverse.map (fun r => r.stepStock (U := U) work hR hQ)).foldr max 0+6*records.length+
            2*(descriptorScheduleTape work PackedNormalizedJob.words records.reverse).length+8)) depth
          (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
          (mk v' {S with R := Function.update S.R result ((List.ofFn fun i => (List.ofFn fun j => cstream A W (tileRows i j)).flatten).flatten++S.R result)}) := by
  dsimp only
  obtain ⟨v',n,rowBatches,hu,hn,he,hrows,hstock⟩ := packedExactRowSchedule_exec (body := body)
    hR hQ hA work hwork src saved count tmp spare result clock savedClock hreg hsep records W hwidth v S
    t ht hp htarget hlocal J hJ rest hblank hleft hscratch hsource hclock hsaved hsavedClock
  obtain ⟨tileRows,hlen,hbytes,hcert⟩ := packedCoreTileRows W records rowBatches J hrows hreplicas hcore
  rw [hbytes] at he hstock
  exact ⟨v',n,tileRows,hu,hn,he,hlen,hcert,hstock⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
