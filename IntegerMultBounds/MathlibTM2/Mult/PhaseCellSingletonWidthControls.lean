module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyWordHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSingletonPublicationControls

/-! Load the two remaining singleton publication dimensions by borrowing
retained unary masters through the existing structural header copier. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem singletonWidthControls_exec (coreBits wordWidth window width tmp saved : Fin T)
    (hreg : [coreBits,wordWidth,window,width,tmp,saved].Nodup)
    (v : HS T Q A U) (S : Stacks T A)
    (hwindow : S.R window = []) (hwidth : S.R width = [])
    (htmp : S.R tmp = []) (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copyWordHeaders tmp saved [(coreBits,window),(wordWidth,width)]) (mk v S)
        (6*(S.R coreBits).length+6*(S.R wordWidth).length+13)
        (mk v' {S with R := (Function.update (Function.update S.R window (S.R coreBits)) width (S.R wordWidth))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v',hu,he⟩ := copyWordHeaders_exec (body := body) tmp saved
    [(coreBits,window),(wordWidth,width)] (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> regs_nodup)
    (by
      intro r hr p hp
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr hp
      rcases hr with rfl | rfl <;> rcases hp with rfl | rfl <;> exact Ne.symm (by assumption))
    S.R v S (by intros; rfl) htmp hsaved
  refine ⟨v',hu,?_⟩
  convert he using 1
  · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    omega
  · simp [copyWordHeadersR,hwindow,hwidth,Function.update_of_ne, *,Ne.symm]

theorem singletonWidthControls_ready {s L : ℕ} {src dst : Fin T}
    (plan : PreparedPublicationPlan T src dst) (coreBits wordWidth tmp saved : Fin T)
    (hreg : [coreBits,wordWidth,plan.window,plan.wordWidth,tmp,saved].Nodup)
    (windows : PublicationWindows s L) (a w : ℕ) (horigin : windows.origins = [a])
    (borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwindow : S.R plan.window = []) (hwidth : S.R plan.wordWidth = [])
    (htmp : S.R tmp = []) (hsaved : S.R saved = [])
    (hcore : (S.R coreBits).length = L*w) (hword : (S.R wordWidth).length = w)
    (hcount : S.R plan.count = [tick])
    (hadv : S.R plan.advances = Mult.ShortConv.gatherControls A [a*w,0]++borrowed)
    (hpad : S.R plan.padRows = [])
    (hfresh : ∀ i ∈ [plan.savedControl,plan.savedAdvances,plan.counter,plan.zero,plan.acc,plan.control,
      plan.trash,plan.tmp,plan.retireCount,plan.gap], S.R i = []) :
    let F : Stacks T A := {S with R := (Function.update
      (Function.update S.R plan.window (S.R coreBits)) plan.wordWidth (S.R wordWidth))}
    ∃ v', v'.user = v.user ∧
      Exec body (copyWordHeaders tmp saved [(coreBits,plan.window),(wordWidth,plan.wordWidth)])
        (mk v S) (6*(L*w)+6*w+13) (mk v' F) ∧ plan.Ready windows w 0 borrowed F := by
  dsimp only
  obtain ⟨v',hu,he⟩ := singletonWidthControls_exec (body := body) coreBits wordWidth
    plan.window plan.wordWidth tmp saved hreg v S hwindow hwidth htmp hsaved
  rw [hcore,hword] at he
  refine ⟨v',hu,he,?_⟩
  have hr := plan.hreg
  regs_ne hr
  apply PreparedPublicationPlan.Ready.singleton plan windows a w horigin
  · simpa [Function.update_of_ne, *,Ne.symm] using hcount
  · simpa [Function.update_of_ne, *,Ne.symm] using hadv
  · simpa [Function.update_of_ne, *,Ne.symm] using hcore
  · simpa [Function.update_of_ne, *,Ne.symm] using hpad
  · simpa using hword
  · intro i hi
    have hoff : i ≠ plan.window ∧ i ≠ plan.wordWidth := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        constructor <;> first | assumption | exact Ne.symm (by assumption)
    simpa [Function.update_of_ne hoff.1,Function.update_of_ne hoff.2] using hfresh i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
