module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowPublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedWindowPublication
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Prepare, publish, and release one arbitrary window class. Only the owned
source prefix and ambient output change; retained gather advances and every
control/scratch tape are restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A s L : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def preparedWindowPublication
    (count savedControl advances savedAdvances counter window zero acc control trash tmp
      padRows wordWidth retireCount gap src dst : Fin T) : Pr P T Q A U :=
  .seq (windowPublicationControls count savedControl advances savedAdvances counter window zero acc control trash tmp)
    (.seq (.seq (retireCountedLine padRows wordWidth src retireCount trash tmp)
      (scatterBatch control savedControl gap window src dst acc trash tmp)) (uclear control))

theorem preparedWindowPublication_exec
    (count savedControl advances savedAdvances counter window zero acc control trash tmp
      padRows wordWidth retireCount gap src dst : Fin T)
    (hreg : [count,savedControl,advances,savedAdvances,counter,window,zero,acc,control,trash,tmp,
      padRows,wordWidth,retireCount,gap,src,dst].Nodup)
    (windows : PublicationWindows s L) (w missing : ℕ) (hw1 : 1 ≤ w)
    (paddedRows rows : List (List GaussianInt))
    (hlen : rows.length = windows.origins.length)
    (hrows : ∀ row ∈ rows, row.length = L) (hpadded : ∀ row ∈ paddedRows, row.length = L)
    (hmissing : missing+rows.length = paddedRows.length)
    (hreal : paddedRows.flatten.drop (missing*L) = rows.flatten)
    (E sourceTail outputTail borrowed : List (Fin (A+4))) (hE : E.length = s*w)
    (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R count = List.replicate windows.origins.length tick)
    (hadvances : S.R advances = gatherControls A (originAdvances w 0 windows.origins++[0])++borrowed)
    (hwindow : (S.R window).length = L*w)
    (hsrc : S.R src = cstream A w paddedRows.flatten++sourceTail) (hdst : S.R dst = E++outputTail)
    (hpadRows : (S.R padRows).length = missing*L) (hwidth : (S.R wordWidth).length = w)
    (hfresh : ∀ i ∈ [savedControl,savedAdvances,counter,zero,acc,control,trash,tmp,retireCount,gap], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ retireCountedLineCost (missing*L) w+72*s*w+31 ∧
      Exec body (preparedWindowPublication count savedControl advances savedAdvances counter window zero acc control trash tmp
        padRows wordWidth retireCount gap src dst) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src sourceTail) dst
          (scatterRows (L*w) E (cstream A w rows.flatten) (windows.gaps w)++outputTail))}) := by
  have hr := hreg
  regs_ne hr
  have hcontrol := hfresh control (by simp)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := windowPublicationControls_exec (body := body)
    count savedControl advances savedAdvances counter window zero acc control trash tmp (by regs_nodup)
    windows w hw1 borrowed v S hcount hadvances hwindow (by
      intro i hi; apply hfresh i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  let M : Stacks T A := {S with R := Function.update S.R control (gatherControls A (windows.gaps w))}
  have he₁' : Exec body (windowPublicationControls count savedControl advances savedAdvances counter window zero acc control trash tmp)
      (mk v S) n₁ (mk v₁ M) := by simpa only [hcontrol,List.append_nil] using he₁
  have hstable (i : Fin T) (hi : i ≠ control) : M.R i = S.R i := by simp [M,hi]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := paddedWindowPublication_exec (body := body)
    padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp (by regs_nodup)
    windows w missing hw1 paddedRows rows hlen hrows hpadded hmissing hreal E sourceTail outputTail hE v₁ M
    (by rw [hstable _ ‹control ≠ src›.symm]; exact hsrc)
    (by rw [hstable _ ‹control ≠ padRows›.symm]; exact hpadRows)
    (by rw [hstable _ ‹control ≠ wordWidth›.symm]; exact hwidth)
    (by simp [M]) (by rw [hstable _ ‹control ≠ dst›.symm]; exact hdst)
    (by rw [hstable _ ‹window ≠ control›]; exact hwindow)
    (by
      intro i hi
      have ho : i ≠ control := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hstable i ho]
      apply hfresh i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  let F : Stacks T A := {M with R := (Function.update (Function.update M.R src sourceTail) dst
    (scatterRows (L*w) E (cstream A w rows.flatten) (windows.gaps w)++outputTail))}
  have hF : F.R control = gatherControls A (windows.gaps w) := by
    simp [F,M,‹control ≠ src›,‹control ≠ dst›]
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := releaseWindowPublicationControls_exec (body := body) control windows w hw1 v₂ F hF
  have hfinal : {F with R := Function.update F.R control []} =
      {S with R := (Function.update (Function.update S.R src sourceTail) dst
        (scatterRows (L*w) E (cstream A w rows.flatten) (windows.gaps w)++outputTail))} := by
    apply Stacks.ext
    · rfl
    · rfl
    · rfl
    funext i
    by_cases hc : i = control
    · subst i; simp [F,M,hcontrol,‹control ≠ src›,‹control ≠ dst›]
    · simp [F,M,hc,Function.update_apply]
  refine ⟨v₃,n₁+(n₂+n₃),hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · nlinarith only [hn₁,hn₂,hn₃]
  · simpa only [preparedWindowPublication,hfinal] using Exec.seq he₁' (Exec.seq he₂ he₃)

theorem preparedWindowPublication_native
    (count savedControl advances savedAdvances counter window zero acc control trash tmp
      padRows wordWidth retireCount gap src dst : Fin T) :
    mnNativePushBound 2 (preparedWindowPublication (P := P) (Q := Q) (A := A) (U := U)
      count savedControl advances savedAdvances counter window zero acc control trash tmp
      padRows wordWidth retireCount gap src dst) := by
  simp [preparedWindowPublication,windowPublicationControls,publicationControls,trimAdvance,trimAdvanceLoopBody,
    gatherRead,gatherReadStep,WordCmd.peekRp,discardPrefix,scatterBatch,scatterLoopBody,scatterPacket,
    retireCountedLine,unaryProduct,scanP,ucopy,umulSym,transfer,moveR,uclear,keepIn,scanR,transferAct,
    drainR,popDo,whileR,moveStep,peekR,pushN,popPush,mnNativePushBound,mnActPush]

theorem preparedWindowPublication_within
    {count savedControl advances savedAdvances counter window zero acc control trash tmp
      padRows wordWidth retireCount gap src dst : Fin T}
    {v v' : HS T Q A U} {S F : Stacks T A} {n missing w : ℕ}
    (he : Exec body (preparedWindowPublication count savedControl advances savedAdvances counter window zero acc control trash tmp
      padRows wordWidth retireCount gap src dst) (mk v S) n (mk v' F))
    (hn : n ≤ retireCountedLineCost (missing*L) w+72*s*w+31) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
      2*(retireCountedLineCost (missing*L) w+72*s*w+31)) depth
      (preparedWindowPublication count savedControl advances savedAdvances counter window zero acc control trash tmp
        padRows wordWidth retireCount gap src dst) (mk v S) n (mk v' F) := by
  exact mn_native_exec_within he 2 (preparedWindowPublication_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
