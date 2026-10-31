module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTransferCountedLine

/-! Publish the first replica and move its completed ambient line to a reversed
accumulator, exposing the next source and destination lines. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement
variable {T Q A s L : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def replicaPublicationStep
    (padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved : Fin T) :
    Pr P T Q A U :=
  .seq (.seq (retireCountedLine padRows wordWidth src retireCount trash tmp)
    (scatterBatch control savedControl gap window src dst acc trash tmp))
    (transferCountedLine lineRows wordWidth dst outAcc retireCount saved tmp)

theorem replicaPublicationStep_exec
    (padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved : Fin T)
    (hreg : [padRows,wordWidth,retireCount,control,savedControl,gap,window,src,dst,acc,trash,tmp,lineRows,outAcc,saved].Nodup)
    (windows : PublicationWindows s L) (w missing : ℕ) (hw1 : 1 ≤ w)
    (r : PublicationReplica A) (hr : r.Valid windows w missing)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = r.input w++sourceTail) (hdst : S.R dst = r.ambient++outputTail)
    (hpadRows : (S.R padRows).length = missing*L) (hwidth : (S.R wordWidth).length = w)
    (hlineRows : (S.R lineRows).length = s)
    (hc : S.R control = gatherControls A (windows.gaps w)) (hw : (S.R window).length = L*w)
    (hclean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,tmp,saved], S.R i = [])
    :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (retireCountedLineCost (missing*L) w+35*s*w+6)+transferCountedLineCost s w ∧
      Exec body (replicaPublicationStep padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved)
        (mk v S) n (mk v' {S with R := (Function.update (Function.update (Function.update S.R src sourceTail)
          dst outputTail) outAcc ((r.output windows w).reverse++S.R outAcc))}) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := paddedWindowPublication_exec (body := body)
    padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp (by regs_nodup)
    windows w missing hw1 r.paddedRows r.rows hr.rowCount hr.rowLength hr.paddedLength
    hr.paddingCount hr.realRows r.ambient sourceTail outputTail hr.ambientLength v S
    hsrc hpadRows hwidth hc hdst hw (by
      intro i hi; apply hclean i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R src sourceTail)
    dst (r.output windows w++outputTail))}
  have hkeep (i : Fin T) (his : i ≠ src) (hid : i ≠ dst) : M.R i = S.R i := by simp [M,his,hid]
  have hcontrols : ∀ i ∈ [lineRows,wordWidth,retireCount,saved,tmp], M.R i = S.R i := by
    intro i hi
    apply hkeep
    all_goals
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      all_goals first | assumption | (apply Ne.symm; assumption)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := transferCountedLine_exec (body := body)
    lineRows wordWidth dst outAcc retireCount saved tmp (by regs_nodup) s w
    (r.output windows w) outputTail hr.output_length v₁ M
    (by rw [hcontrols _ (by simp)]; exact hlineRows)
    (by rw [hcontrols _ (by simp)]; exact hwidth) (by simp [M])
    (by rw [hcontrols _ (by simp)]; exact hclean _ (by simp))
    (by rw [hcontrols _ (by simp)]; exact hclean _ (by simp))
    (by rw [hcontrols _ (by simp)]; exact hclean _ (by simp))
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_⟩
  have he := Exec.seq he₁ he₂
  simpa [replicaPublicationStep,M,PublicationReplica.output,‹src ≠ outAcc›.symm,‹dst ≠ outAcc›.symm] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
