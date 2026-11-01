module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorEmit
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedDescriptorBank

/-! Serialize any live finite register bank and generate its one-record clock.
Both packed-core and full-period suppliers use the same physical operation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {N T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def prepareDescriptorBank (source : Fin N → Fin T) (dst tmp saved clock : Fin T) : Pr P T Q A U :=
  .seq (emitDescriptorBank dst tmp saved (List.ofFn source))
    (.act (.push (.rt clock) (fun _ => tick) .done))

theorem descriptorBankTape_sources_eq (source work : Fin N → Fin T) (words : Fin N → List (Fin (A+4)))
    (R : Regs T A) (hwords : ∀ i, R (source i) = words i) :
    descriptorBankTape ((List.ofFn source).map (fun i => (i,R i))) =
      descriptorBankTape (placedDescriptorFields work words) := by
  simp only [placedDescriptorFields,descriptorBankTape,List.flatMap_def,List.map_ofFn,
    Function.comp_def,hwords]

theorem prepareDescriptorBank_prepend_exec (source : Fin N → Fin T) (dst tmp saved clock : Fin T)
    (hregs : ∀ i, [source i,dst,tmp,saved].Nodup) (hclockDst : clock ≠ dst)
    (v : HS T Q A U) (S : Stacks T A) (htmp : S.R tmp = []) (hsaved : S.R saved = [])
    (depth : ℕ) :
    let tape := descriptorBankTape ((List.ofFn source).map (fun i => (i,S.R i)))
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+(22*tape.length+4)) depth
        (prepareDescriptorBank source dst tmp saved clock) (Host.mk v S)
        (emitDescriptorBankCost S.R (List.ofFn source)+1)
        (Host.mk v' {S with R := (Function.update (Function.update S.R dst (tape++S.R dst)) clock (tick::S.R clock))}) := by
  dsimp only
  have hreg : ∀ i ∈ List.ofFn source, [i,dst,tmp,saved].Nodup := by
    intro i hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    exact hregs j
  obtain ⟨v',hu,he⟩ := emitDescriptorBank_exec (body := body) dst tmp saved
    (List.ofFn source) hreg v S htmp hsaved
  let tape := descriptorBankTape ((List.ofFn source).map (fun i => (i,S.R i)))
  let M : Stacks T A := {S with R := Function.update S.R dst (tape++S.R dst)}
  let F : Stacks T A := {M with R := Function.update M.R clock (tick::S.R clock)}
  have hclockM : M.R clock = S.R clock := Function.update_of_ne hclockDst _ _
  have hstep : Exec body (.act (.push (.rt clock) (fun _ => tick) .done))
      (Host.mk v' M) 1 (Host.mk v' F) := by
    simpa only [F,Host.mk,Action.run,update_rt,get_rt,hclockM] using
      Exec.act (body := body) (.push (.rt clock) (fun _ => tick) .done) (Host.mk v' M)
  refine ⟨v',hu,?_⟩
  apply mn_native_exec_within (Exec.seq he hstep) 2
  · exact ⟨emitDescriptorBank_native _ _ _ _,by simp [mnNativePushBound,mnActPush]⟩
  · have hc := emitDescriptorBankCost_le S.R (List.ofFn source)
    omega

theorem prepareDescriptorBank_exec (source : Fin N → Fin T) (dst tmp saved clock : Fin T)
    (hregs : ∀ i, [source i,dst,tmp,saved].Nodup) (hclockDst : clock ≠ dst)
    (v : HS T Q A U) (S : Stacks T A) (htmp : S.R tmp = []) (hsaved : S.R saved = [])
    (hclock : S.R clock = []) (depth : ℕ) :
    let tape := descriptorBankTape ((List.ofFn source).map (fun i => (i,S.R i)))
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+(22*tape.length+4)) depth
        (prepareDescriptorBank source dst tmp saved clock) (Host.mk v S)
        (emitDescriptorBankCost S.R (List.ofFn source)+1)
        (Host.mk v' {S with R := (Function.update (Function.update S.R dst (tape++S.R dst)) clock [tick])}) := by
  obtain ⟨v',hu,he⟩ := prepareDescriptorBank_prepend_exec (body := body) source dst tmp saved clock
    hregs hclockDst v S htmp hsaved depth
  exact ⟨v',hu,by simpa only [hclock] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
