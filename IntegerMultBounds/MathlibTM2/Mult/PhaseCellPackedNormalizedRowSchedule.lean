module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedJobSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedRows

/-! The actual restoring packed schedule returns certified coefficient rows
with the original time and peak-stock contracts, without an archive scan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem packedNormalizedRowSchedule_exec
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (work : Fin 325 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (records : List (PackedNormalizedJob A s)) (W : ℕ) (hwidth : ∀ r ∈ records, r.W = W) (v : HS T Q A U) (S : Stacks T A)
    (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hsource : S.R src = descriptorScheduleTape work PackedNormalizedJob.words records++rest)
    (hclock : (S.R clock).length = records.length) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) :
    let step := packedNormalizedDescriptorStep (P := P) (U := U) (A := A) work src saved count tmp spare result hR hQ
    ∃ v' n, ∃ rowBatches : List (List (List GaussianInt)), v'.user = v.user ∧
      n ≤ (records.map (fun r => takeDescriptorBankCost (placedDescriptorFields work r.words)+
        r.setupTime+r.cleanup (U := U) hR hQ+3)).sum+
        (records.map (fun r => r.Fs.length*r.replicaTime)).sum+6*records.length+
        2*(descriptorScheduleTape work PackedNormalizedJob.words records).length+10 ∧
      Exec body (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
        (mk v' {S with R := Function.update S.R result ((rowBatches.reverse.map (fun rows => cstream A W rows.flatten)).flatten++S.R result)}) ∧
      List.Forall₂ PackedNormalizedJob.RowOutput records rowBatches ∧
      ∀ C, mnProgPush (descriptorSolverSchedule src saved tmp clock savedClock step) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*((records.map PackedNormalizedJob.outputVolume).sum+(records.map (fun r => r.stepStock (U := U) work hR hQ)).foldr max 0+6*records.length+
            2*(descriptorScheduleTape work PackedNormalizedJob.words records).length+8)) depth
          (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
          (mk v' {S with R := Function.update S.R result ((rowBatches.reverse.map (fun rows => cstream A W rows.flatten)).flatten++S.R result)}) := by
  dsimp only
  obtain ⟨v',n,outputs,hu,hn,he,hgood,hstock⟩ := packedNormalizedJobSchedule_exec (body := body)
    hR hQ hA work hwork src saved count tmp spare result clock savedClock hreg hsep records v S rest
    hblank hleft hscratch hsource hclock hsaved hsavedClock
  obtain ⟨rowBatches,houtputs,hrows⟩ := PackedNormalizedJob.outputs_rows W hwidth hgood
  rw [houtputs,←List.map_reverse] at he hstock
  exact ⟨v',n,rowBatches,hu,hn,he,hrows,hstock⟩

/-! Running descriptors in reverse produces the requested core order directly,
without an additional physical archive reversal. -/
theorem packedNormalizedRowSchedule_ordered_exec
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (work : Fin 325 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (records : List (PackedNormalizedJob A s)) (W : ℕ) (hwidth : ∀ r ∈ records, r.W = W) (v : HS T Q A U) (S : Stacks T A)
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
      List.Forall₂ PackedNormalizedJob.RowOutput records rowBatches ∧
      ∀ C, mnProgPush (descriptorSolverSchedule src saved tmp clock savedClock step) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*((records.reverse.map PackedNormalizedJob.outputVolume).sum+(records.reverse.map (fun r => r.stepStock (U := U) work hR hQ)).foldr max 0+6*records.length+
            2*(descriptorScheduleTape work PackedNormalizedJob.words records.reverse).length+8)) depth
          (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
          (mk v' {S with R := Function.update S.R result ((rowBatches.map (fun rows => cstream A W rows.flatten)).flatten++S.R result)}) := by
  dsimp only
  obtain ⟨v',n,rowBatches,hu,hn,he,hgood,hstock⟩ := packedNormalizedRowSchedule_exec (body := body)
    hR hQ hA work hwork src saved count tmp spare result clock savedClock hreg hsep records.reverse W
    (by intro r hr; exact hwidth r (List.mem_reverse.mp hr)) v S rest hblank hleft hscratch hsource
    (by simpa only [List.length_reverse] using hclock) hsaved hsavedClock
  refine ⟨v',n,rowBatches.reverse,hu,?_,?_,?_,?_⟩
  · simpa only [List.length_reverse] using hn
  · exact he
  · simpa only [List.reverse_reverse] using List.rel_reverse hgood
  · intro C hp hb depth
    simpa only [List.length_reverse] using hstock C hp hb depth

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
