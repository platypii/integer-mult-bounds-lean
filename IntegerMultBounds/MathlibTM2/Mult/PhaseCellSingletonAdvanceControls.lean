module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSingletonPublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

/-! Turn the boundary counter's unary skip into restoring singleton advances.
The skip is borrowed and restored; only the control destination changes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def singletonAdvanceControls (skip dst tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (.push (.rt dst) (fun _ => blank)
    (.push (.rt dst) (fun _ => blank) .done))) (ucopy skip dst tmp)

theorem singletonAdvanceControls_exec (skip dst tmp : Fin T)
    (hsd : skip ≠ dst) (hst : skip ≠ tmp) (hdt : dst ≠ tmp)
    (v : HS T Q A U) (S : Stacks T A) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (singletonAdvanceControls skip dst tmp) (mk v S) (4*(S.R skip).length+5)
        (mk v' {S with R := (Function.update S.R dst
          (gatherControls A [(S.R skip).length,0]++S.R dst))}) := by
  let M : Stacks T A := {S with R := (Function.update S.R dst (blank::blank::S.R dst))}
  have hp : Exec body (.act (.push (.rt dst) (fun _ => blank)
      (.push (.rt dst) (fun _ => blank) .done))) (mk v S) 1 (mk v M) := by
    simpa [M,Action.run,update_rt,Function.update_idem] using
      (Exec.act (body := body) (.push (.rt dst) (fun _ => blank)
        (.push (.rt dst) (fun _ => blank) .done)) (mk v S))
  obtain ⟨v',hu,he⟩ := ucopy_exec (body := body) hsd hst hdt v M
    (by simpa [M,hdt.symm] using htmp)
  refine ⟨v',hu,?_⟩
  have hex := Exec.seq hp he
  have htime : 1+(4*(M.R skip).length+4) = 4*(S.R skip).length+5 := by
    simp only [M,Function.update_of_ne hsd]
    omega
  rw [htime] at hex
  simpa [singletonAdvanceControls,M,hsd,gatherControls,Function.update_idem,List.append_assoc,
    Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hex

def prepareSingletonPublication {src dst : Fin T}
    (plan : PreparedPublicationPlan T src dst) (skip tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (.push (.rt plan.count) (fun _ => tick) .done))
    (singletonAdvanceControls skip plan.advances tmp)

/-- The executed builder establishes the publication contract on its actual
returned state. All other controls are supplied in their ordinary unary form. -/
theorem singletonAdvanceControls_ready {s L : ℕ} {src dst : Fin T}
    (plan : PreparedPublicationPlan T src dst) (skip tmp : Fin T)
    (hsd : skip ≠ plan.advances) (hst : skip ≠ tmp) (hdt : plan.advances ≠ tmp)
    (hskipCount : skip ≠ plan.count) (htmpCount : tmp ≠ plan.count)
    (windows : PublicationWindows s L) (a w : ℕ) (horigin : windows.origins = [a])
    (v : HS T Q A U) (S : Stacks T A) (htmp : S.R tmp = [])
    (hskip : (S.R skip).length = a*w)
    (hcount : S.R plan.count = [])
    (hwindow : (S.R plan.window).length = L*w)
    (hpad : S.R plan.padRows = []) (hwidth : (S.R plan.wordWidth).length = w)
    (hfresh : ∀ i ∈ [plan.savedControl,plan.savedAdvances,plan.counter,plan.zero,plan.acc,plan.control,
      plan.trash,plan.tmp,plan.retireCount,plan.gap], S.R i = []) :
    let F : Stacks T A := {S with R := (Function.update (Function.update S.R plan.count [tick]) plan.advances
      (gatherControls A [a*w,0]++S.R plan.advances))}
    ∃ v', v'.user = v.user ∧
      Exec body (prepareSingletonPublication plan skip tmp) (mk v S) (1+(4*(a*w)+5)) (mk v' F) ∧
      plan.Ready windows w 0 (S.R plan.advances) F := by
  dsimp only
  let M : Stacks T A := {S with R := (Function.update S.R plan.count [tick])}
  have hp : Exec body (.act (.push (.rt plan.count) (fun _ => tick) .done))
      (mk v S) 1 (mk v M) := by
    simpa [M,Action.run,update_rt,hcount] using
      (Exec.act (body := body) (.push (.rt plan.count) (fun _ => tick) .done) (mk v S))
  obtain ⟨v',hu,he⟩ := singletonAdvanceControls_exec (body := body) skip plan.advances tmp
    hsd hst hdt v M (by simpa [M,htmpCount] using htmp)
  have hm : (M.R skip).length = a*w := by simpa [M,hskipCount] using hskip
  rw [hm] at he
  have hr := plan.hreg
  regs_ne hr
  simp only [M,Function.update_of_ne ‹plan.count ≠ plan.advances›.symm] at he
  refine ⟨v',hu,Exec.seq hp he,?_⟩
  apply PreparedPublicationPlan.Ready.singleton plan windows a w horigin
  · simp [Function.update_of_ne, *,Ne.symm]
  · simp
  · simpa [Function.update_of_ne, *,Ne.symm] using hwindow
  · simpa [Function.update_of_ne, *,Ne.symm] using hpad
  · simpa [Function.update_of_ne, *,Ne.symm] using hwidth
  · intro i hi
    have hne : i ≠ plan.advances := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | assumption | exact Ne.symm (by assumption)
    have hnc : i ≠ plan.count := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Ne.symm (by assumption)
    simpa [Function.update_of_ne hne,Function.update_of_ne hnc] using hfresh i hi

/-- The two sentinel pushes are the largest single action in this builder. -/
theorem singletonAdvanceControls_native (skip dst tmp : Fin T) :
    mnNativePushBound 2 (singletonAdvanceControls (P := P) (Q := Q) (A := A) (U := U) skip dst tmp) := by
  simp [singletonAdvanceControls,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem singletonAdvanceControls_within (skip dst tmp : Fin T)
    (v v' : HS T Q A U) (S F : Stacks T A) (n depth : ℕ)
    (he : Exec body (singletonAdvanceControls skip dst tmp) (mk v S) n (mk v' F)) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*n) depth
      (singletonAdvanceControls skip dst tmp) (mk v S) n (mk v' F) :=
  mn_native_exec_within he 2 (singletonAdvanceControls_native skip dst tmp) depth _ (by omega)

theorem prepareSingletonPublication_native {src dst : Fin T}
    (plan : PreparedPublicationPlan T src dst) (skip tmp : Fin T) :
    mnNativePushBound 2 (prepareSingletonPublication (P := P) (Q := Q) (A := A) (U := U) plan skip tmp) := by
  exact ⟨by simp [mnNativePushBound,mnActPush],singletonAdvanceControls_native skip plan.advances tmp⟩

theorem prepareSingletonPublication_within {src dst : Fin T}
    (plan : PreparedPublicationPlan T src dst) (skip tmp : Fin T)
    (v v' : HS T Q A U) (S F : Stacks T A) (n depth : ℕ)
    (he : Exec body (prepareSingletonPublication plan skip tmp) (mk v S) n (mk v' F)) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*n) depth
      (prepareSingletonPublication plan skip tmp) (mk v S) n (mk v' F) :=
  mn_native_exec_within he 2 (prepareSingletonPublication_native plan skip tmp) depth _ (by omega)

/-- Remove exactly the generated advance prefix, restoring its borrowed suffix. -/
def retireSingletonAdvances (skip dst tmp : Fin T) : Pr P T Q A U :=
  .seq (usub skip dst tmp) (.act (dropTop dst (dropTop dst .done)))

theorem retireSingletonAdvances_exec (skip dst tmp : Fin T)
    (hsd : skip ≠ dst) (hst : skip ≠ tmp) (hdt : dst ≠ tmp)
    (v : HS T Q A U) (S : Stacks T A) (htmp : S.R tmp = [])
    (tail : List (Fin (A+4)))
    (hdst : S.R dst = gatherControls A [(S.R skip).length,0]++tail) :
    ∃ v', v'.user = v.user ∧
      Exec body (retireSingletonAdvances skip dst tmp) (mk v S) (4*(S.R skip).length+5)
        (mk v' {S with R := (Function.update S.R dst tail)}) := by
  obtain ⟨v',hu,he⟩ := usub_exec (body := body) hsd hst hdt v S htmp
  have hdrop : (S.R dst).drop (S.R skip).length = blank::blank::tail := by
    rw [hdst]
    simp [gatherControls,List.append_assoc]
  rw [hdrop] at he
  have hp := Exec.act (body := body) (dropTop dst (dropTop dst .done))
    (mk v' {S with R := (Function.update S.R dst (blank::blank::tail))})
  refine ⟨v',hu,?_⟩
  have hex := Exec.seq he hp
  simpa [retireSingletonAdvances,dropTop,Action.run,update_rt,Function.update_idem,
    Nat.add_assoc] using hex

theorem retireSingletonAdvances_native (skip dst tmp : Fin T) :
    mnNativePushBound 1 (retireSingletonAdvances (P := P) (Q := Q) (A := A) (U := U) skip dst tmp) := by
  simp [retireSingletonAdvances,usub,scanR,drainR,popDo,keepIn,dropTop,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

/-- Retirement uses the same actual trace and charges no independent stock
certificate to the caller. -/
theorem retireSingletonAdvances_within (skip dst tmp : Fin T)
    (v v' : HS T Q A U) (S F : Stacks T A) (n depth : ℕ)
    (he : Exec body (retireSingletonAdvances skip dst tmp) (mk v S) n (mk v' F)) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+n) depth
      (retireSingletonAdvances skip dst tmp) (mk v S) n (mk v' F) :=
  mn_native_exec_within he 1 (retireSingletonAdvances_native skip dst tmp) depth _ (by omega)

-- The concrete source/destination composition is proved directly in
-- PhaseCellSeamPublicationRetirement; no generic middle-execution contract is needed.

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
