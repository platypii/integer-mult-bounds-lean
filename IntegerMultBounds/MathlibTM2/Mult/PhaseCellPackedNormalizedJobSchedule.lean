module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedJob
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorSolverSchedule

/-! A fixed restoring descriptor schedule executes mathematically certified
packed jobs. Neither the job record nor this theorem assumes solver executions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem packedNormalizedJob_step_exec (r : PackedNormalizedJob A s)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (work : Fin 325 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result : Fin T) (hreg : [src,saved,count,tmp,spare,result].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result])
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hsource : S.R src = descriptorBankTape (placedDescriptorFields work r.words)++tail)
    (hcount : S.R count = []) (htmp : S.R tmp = []) (hspare : S.R spare = []) :
    ∃ v' n output, v'.user = v.user ∧ n ≤ r.stepTime (U := U) work hR hQ ∧
      Exec body (packedNormalizedDescriptorStep work src saved count tmp spare result hR hQ) (mk v S) n
        (mk v' (dispatchedDescriptorState work r.words src saved result tail output S)) ∧ r.output output ∧
      ∀ C, mnProgPush (packedNormalizedDescriptorStep (P := P) (U := U) (A := A)
          work src saved count tmp spare result hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*r.stepStock (U := U) work hR hQ) depth
          (packedNormalizedDescriptorStep work src saved count tmp spare result hR hQ) (mk v S) n
          (mk v' (dispatchedDescriptorState work r.words src saved result tail output S)) := by
  let Hbase : Stacks 242 A := ⟨S.inp,S.out,fun _ => [],fun _ => []⟩
  have hwords : packedNormalizedFactoryPacketWords Hbase r.Bcore r.V r.p r.u r.l r.targetOut s r.t r.a r.b
      r.coreWidth r.k r.radius r.W r.Fs = r.words :=
    packedNormalizedFactoryPacketWords_host Hbase PackedNormalizedJob.emptyHost _ _ _ _ _ _ _ _ _ _ _ _ _ _ r.Fs
  have hstock : registerBankStock
      (packedNormalizedFactoryInput Hbase r.Bcore r.V r.p r.u r.l r.targetOut s r.t r.a r.b
        r.coreWidth r.k r.radius r.W r.Fs) = registerBankStock r.initial := by
    rw [packedNormalizedFactoryInput_host Hbase PackedNormalizedJob.emptyHost]
    rfl
  obtain ⟨v',n,output,hu,hn,he,hp,ht⟩ := packedNormalizedFactoryDescriptorStep_exec Hbase r.bounds
    hR hQ hA r.Bcore r.hsCore r.q r.W r.hqSizing r.hpq r.hW r.Fs r.hF r.coreWidth r.k r.radius
    r.haEq r.hbEq r.hleft r.hright r.hcoeff r.hvaluesFit r.hbandRoom r.hgeometryRoom r.hprecisionRoom
    r.localityTarget r.hhalo r.Y r.hY work hwork src saved count tmp spare result hreg hsep body v S
    rfl rfl hblank hleft tail (by rw [hwords]; exact hsource) hcount htmp hspare
  rw [hwords] at hn he ht
  rw [hstock, r.initialStock] at hn ht
  exact ⟨v',n,output,hu,hn,he,hp,ht⟩

/-- A list of actual packed jobs restores its descriptor tape, clock, private
bank and host frame, accumulating only certified result words. -/
theorem packedNormalizedJobSchedule_exec
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (work : Fin 325 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (records : List (PackedNormalizedJob A s)) (v : HS T Q A U) (S : Stacks T A)
    (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hsource : S.R src = descriptorScheduleTape work PackedNormalizedJob.words records++rest)
    (hclock : (S.R clock).length = records.length) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) :
    let step := packedNormalizedDescriptorStep (P := P) (U := U) (A := A) work src saved count tmp spare result hR hQ
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (records.map (fun r => r.stepTime (U := U) work hR hQ+3)).sum+6*records.length+
        2*(descriptorScheduleTape work PackedNormalizedJob.words records).length+10 ∧
      Exec body (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
        (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) ∧
      List.Forall₂ PackedNormalizedJob.output records outputs ∧
      ∀ C, mnProgPush (descriptorSolverSchedule src saved tmp clock savedClock step) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*((records.map (fun r => r.stepStock (U := U) work hR hQ)).sum+6*records.length+
            2*(descriptorScheduleTape work PackedNormalizedJob.words records).length+8)) depth
          (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
          (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) := by
  have hreg' : [src,saved,count,tmp,spare,result].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hreg ⊢
    tauto
  have hsep' (i : Fin 325) : work i ∉ [src,saved,count,tmp,spare,result] := by
    have hi := hsep i
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi ⊢
    tauto
  exact descriptorSolverSchedule_exec_trace_on (body := body) work hwork (id : Fin 325 → Fin 325)
    src saved count tmp spare result clock savedClock hreg hsep PackedNormalizedJob.words
    (packedNormalizedDescriptorStep work src saved count tmp spare result hR hQ)
    (fun r => r.stepTime (U := U) work hR hQ) (fun r => r.stepStock (U := U) work hR hQ)
    PackedNormalizedJob.output records v S
    (by
      intro r _ vi Si tail hb hl hs hc ht hp
      exact packedNormalizedJob_step_exec (body := body) r hR hQ hA work hwork
        src saved count tmp spare result hreg' hsep' vi Si tail hb hl hs hc ht hp)
    rest hblank hleft hscratch hsource hclock hsaved hsavedClock

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
