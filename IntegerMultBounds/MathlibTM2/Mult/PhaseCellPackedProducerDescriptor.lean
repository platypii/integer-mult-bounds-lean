module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedProducerPlan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorEmit

/-! Produce the next ordinary packed descriptor and its runtime clock from a
live borrowed bank. The caller supplies word contents, not a serialized queue. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedProducerPlan
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def prepareDescriptor (plan : PackedProducerPlan T Q) (source : Fin 325 → Fin T) : Pr P T Q A U :=
  .seq (emitDescriptorBank plan.src plan.tmp plan.saved (List.ofFn source))
    (.act (.push (.rt plan.clock) (fun _ => tick) .done))

theorem prepareDescriptor_exec (plan : PackedProducerPlan T Q) (r : PackedNormalizedJob A s)
    (source : Fin 325 → Fin T)
    (hsourceReg : ∀ i, [source i,plan.src,plan.tmp,plan.saved].Nodup)
    (v : HS T Q A U) (S : Stacks T A)
    (hwords : ∀ i, S.R (source i) = r.words i)
    (hblank : ∀ i, S.R (plan.work i) = []) (hleft : ∀ i, S.L (plan.work i) = [])
    (hscratch : ∀ k ∈ [plan.count,plan.tmp,plan.spare], S.R k = [])
    (hclock : S.R plan.clock = []) (hsaved : S.R plan.saved = []) (hsavedClock : S.R plan.savedClock = [])
    (depth : ℕ) :
    let tape := descriptorScheduleTape plan.work PackedNormalizedJob.words [r]
    let F := {S with R := (Function.update (Function.update S.R plan.src (tape++S.R plan.src)) plan.clock [tick])}
    ∃ v', v'.user = v.user ∧ plan.Ready [r] (S.R plan.src) F ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+22*tape.length+4) depth
        (plan.prepareDescriptor source) (Host.mk v S) (emitDescriptorBankCost S.R (List.ofFn source)+1) (Host.mk v' F) := by
  dsimp only
  have hr := plan.hreg
  regs_ne hr
  have htmp := hscratch plan.tmp (by simp)
  have hreg : ∀ i ∈ List.ofFn source, [i,plan.src,plan.tmp,plan.saved].Nodup := by
    intro i hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    exact hsourceReg j
  have htape : descriptorBankTape ((List.ofFn source).map (fun i => (i,S.R i))) =
      descriptorScheduleTape plan.work PackedNormalizedJob.words [r] := by
    simp only [descriptorScheduleTape,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
      placedDescriptorFields,descriptorBankTape,List.flatMap_def,List.map_ofFn,Function.comp_def,hwords]
  let tape := descriptorScheduleTape plan.work PackedNormalizedJob.words [r]
  let M : Stacks T A := {S with R := Function.update S.R plan.src (tape++S.R plan.src)}
  let F : Stacks T A := {M with R := Function.update M.R plan.clock [tick]}
  obtain ⟨v',hu,he⟩ := emitDescriptorBank_exec (body := body) plan.src plan.tmp plan.saved
    (List.ofFn source) hreg v S htmp hsaved
  rw [htape] at he
  have hclockM : M.R plan.clock = [] :=
    (Function.update_of_ne ‹plan.src ≠ plan.clock›.symm _ _).trans hclock
  have hstep : Exec body (.act (.push (.rt plan.clock) (fun _ => tick) .done)) (Host.mk v' M) 1 (Host.mk v' F) := by
    simpa only [F,Host.mk,Action.run,update_rt,get_rt,hclockM] using
      Exec.act (body := body) (.push (.rt plan.clock) (fun _ => tick) .done) (Host.mk v' M)
  have hwhole := Exec.seq he hstep
  have hframe (i : Fin T) (his : i ≠ plan.src) (hic : i ≠ plan.clock) : F.R i = S.R i := by
    simp only [F,M,Function.update_of_ne his,Function.update_of_ne hic]
  refine ⟨v',hu,?_,?_⟩
  · constructor
    · intro i
      rw [hframe _ (by intro hh; exact plan.hsep i (by simp [hh])) (by intro hh; exact plan.hsep i (by simp [hh]))]
      exact hblank i
    · exact hleft
    · intro i hi
      have his : i ≠ plan.src := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl <;> first | assumption | (apply Ne.symm; assumption)
      have hic : i ≠ plan.clock := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl <;> assumption
      rw [hframe i his hic]
      exact hscratch i hi
    · simp only [Function.update_of_ne ‹plan.src ≠ plan.clock›,Function.update_self,List.reverse_cons,List.reverse_nil,List.nil_append]
    · simp
    · rw [hframe _ ‹plan.src ≠ plan.saved›.symm ‹plan.saved ≠ plan.clock›]
      exact hsaved
    · rw [hframe _ ‹plan.src ≠ plan.savedClock›.symm ‹plan.clock ≠ plan.savedClock›.symm]
      exact hsavedClock
  · apply mn_native_exec_within hwhole 2
    · exact ⟨emitDescriptorBank_native _ _ _ _,by simp [mnNativePushBound,mnActPush]⟩
    · have hc := emitDescriptorBankCost_le S.R (List.ofFn source)
      rw [htape] at hc
      omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedProducerPlan
