module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSingletonWidthControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSingletonAdvanceControls

/-! Execute all singleton publication control placement from retained masters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s L : ℕ} {P U : Type} {body : P → Pr P T Q A U} {src dst : Fin T}

def singletonPublicationSetup (plan : PreparedPublicationPlan T src dst)
    (coreBits wordWidth skip tmp saved : Fin T) : Pr P T Q A U :=
  .seq (copyWordHeaders tmp saved [(coreBits,plan.window),(wordWidth,plan.wordWidth)])
    (prepareSingletonPublication plan skip tmp)

def singletonPublicationSetupState (plan : PreparedPublicationPlan T src dst)
    (coreBits wordWidth : Fin T) (a w : ℕ) (S : Stacks T A) : Stacks T A :=
  let M : Stacks T A := {S with R := (Function.update
    (Function.update S.R plan.window (S.R coreBits)) plan.wordWidth (S.R wordWidth))}
  {M with R := (Function.update (Function.update M.R plan.count [tick])
    plan.advances (gatherControls A [a*w,0]++M.R plan.advances))}

theorem singletonPublicationSetupState_off (plan : PreparedPublicationPlan T src dst)
    (coreBits wordWidth : Fin T) (a w : ℕ) (S : Stacks T A) (i : Fin T)
    (hi : i ∉ [plan.count,plan.window,plan.wordWidth,plan.advances]) :
    (singletonPublicationSetupState plan coreBits wordWidth a w S).R i = S.R i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
  simp [singletonPublicationSetupState,Function.update_of_ne,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2]

/-- Data-port updates commute with setup when they avoid its controls and masters. -/
theorem singletonPublicationSetupState_update_off (plan : PreparedPublicationPlan T src dst)
    (coreBits wordWidth : Fin T) (a w : ℕ) (S : Stacks T A) (i : Fin T)
    (hi : i ∉ [plan.count,plan.window,plan.wordWidth,plan.advances,coreBits,wordWidth])
    (xs : List (Fin (A+4))) :
    singletonPublicationSetupState plan coreBits wordWidth a w {S with R := (Function.update S.R i xs)} =
      {singletonPublicationSetupState plan coreBits wordWidth a w S with R :=
        (Function.update (singletonPublicationSetupState plan coreBits wordWidth a w S).R i xs)} := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
  rcases hi with ⟨hc,hw,hwidth,ha,hcore,hword⟩
  refine Stacks.ext rfl rfl rfl ?_
  funext j
  by_cases hj : j = i
  · subst j
    simp [singletonPublicationSetupState,Function.update_of_ne,hc,hw,hwidth,ha,
      Ne.symm hcore,Ne.symm hword]
  · simp [singletonPublicationSetupState,Function.update_apply,hj,Ne.symm hcore,Ne.symm hword,Ne.symm ha]

theorem singletonPublicationSetup_exec (plan : PreparedPublicationPlan T src dst)
    (coreBits wordWidth skip tmp saved : Fin T)
    (hreg : (plan.support++[coreBits,wordWidth,skip,tmp,saved]).Nodup)
    (windows : PublicationWindows s L) (a w : ℕ) (horigin : windows.origins = [a])
    (v : HS T Q A U) (S : Stacks T A)
    (hcore : (S.R coreBits).length = L*w) (hword : (S.R wordWidth).length = w)
    (hskip : (S.R skip).length = a*w)
    (hfresh : ∀ i ∈ plan.support, i ≠ plan.advances → S.R i = [])
    (htmp : S.R tmp = []) (hsaved : S.R saved = []) (depth : ℕ) :
    let F := singletonPublicationSetupState plan coreBits wordWidth a w S
    ∃ v' n, v'.user = v.user ∧ n = (6*(L*w)+6*w+13)+(1+(4*(a*w)+5)) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*n) depth
        (singletonPublicationSetup plan coreBits wordWidth skip tmp saved) (mk v S) n (mk v' F) ∧
      plan.Ready windows w 0 (S.R plan.advances) F := by
  dsimp only [singletonPublicationSetupState]
  have hr := hreg
  simp only [PreparedPublicationPlan.support,List.cons_append,List.append_nil,List.nil_append] at hr
  regs_ne hr
  have hblank (i) (hi : i ∈ plan.support) (hne : i ≠ plan.advances) := hfresh i hi hne
  have hw0 : S.R plan.window = [] := hblank _ (by simp [PreparedPublicationPlan.support]) (by first | assumption | exact Ne.symm (by assumption))
  have hwidth0 : S.R plan.wordWidth = [] := hblank _ (by simp [PreparedPublicationPlan.support]) (Ne.symm (by first | assumption | exact Ne.symm (by assumption)))
  obtain ⟨u,hu,he⟩ := singletonWidthControls_exec (body := body) coreBits wordWidth
    plan.window plan.wordWidth tmp saved (by regs_nodup) v S hw0 hwidth0 htmp hsaved
  rw [hcore,hword] at he
  let M : Stacks T A := {S with R := (Function.update
    (Function.update S.R plan.window (S.R coreBits)) plan.wordWidth (S.R wordWidth))}
  obtain ⟨v',hv,hprepare,hready⟩ := singletonAdvanceControls_ready (body := body) plan skip tmp
    (by first | assumption | exact Ne.symm (by assumption)) (by first | assumption | exact Ne.symm (by assumption)) (by first | assumption | exact Ne.symm (by assumption)) (Ne.symm (by first | assumption | exact Ne.symm (by assumption))) (Ne.symm (by first | assumption | exact Ne.symm (by assumption)))
    windows a w horigin u M
    (by simpa [M,Function.update_of_ne, *,Ne.symm] using htmp)
    (by simpa [M,Function.update_of_ne, *,Ne.symm] using hskip)
    (by simpa [M,Function.update_of_ne, *,Ne.symm] using
      hblank plan.count (by simp [PreparedPublicationPlan.support]) (by first | assumption | exact Ne.symm (by assumption)))
    (by simpa [M,Function.update_of_ne, *,Ne.symm] using hcore)
    (by simpa [M,Function.update_of_ne, *,Ne.symm] using
      hblank plan.padRows (by simp [PreparedPublicationPlan.support]) (Ne.symm (by first | assumption | exact Ne.symm (by assumption))))
    (by simpa [M] using hword)
    (by
      intro i hi
      have hoff : i ≠ plan.window ∧ i ≠ plan.wordWidth ∧ i ≠ plan.advances := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          refine ⟨?_,?_,?_⟩ <;> first | assumption | exact Ne.symm (by first | assumption | exact Ne.symm (by assumption))
      simpa [M,Function.update_of_ne hoff.1,Function.update_of_ne hoff.2.1] using
        hblank i (by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [PreparedPublicationPlan.support]) hoff.2.2)
  refine ⟨v',_,hv.trans hu,rfl,?_,?_⟩
  · apply mn_native_exec_within (Exec.seq he hprepare) 2
    · exact ⟨copyWordHeaders_native _ _ _,prepareSingletonPublication_native plan skip tmp⟩
    · omega
  · simpa [M,Function.update_of_ne, *,Ne.symm] using hready

theorem singletonPublicationSetup_native (plan : PreparedPublicationPlan T src dst)
    (coreBits wordWidth skip tmp saved : Fin T) :
    mnNativePushBound 2 (singletonPublicationSetup (P := P) (Q := Q) (A := A) (U := U)
      plan coreBits wordWidth skip tmp saved) :=
  ⟨copyWordHeaders_native _ _ _,prepareSingletonPublication_native plan skip tmp⟩

theorem singletonPublicationSetup_within (plan : PreparedPublicationPlan T src dst)
    (coreBits wordWidth skip tmp saved : Fin T)
    (v v' : HS T Q A U) (S F : Stacks T A) (n depth : ℕ)
    (he : Exec body (singletonPublicationSetup plan coreBits wordWidth skip tmp saved)
      (mk v S) n (mk v' F)) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*n) depth
      (singletonPublicationSetup plan coreBits wordWidth skip tmp saved) (mk v S) n (mk v' F) :=
  mn_native_exec_within he 2 (singletonPublicationSetup_native plan coreBits wordWidth skip tmp saved)
    depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
