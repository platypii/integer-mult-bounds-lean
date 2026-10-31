module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationData

/-! Compact publication uses the retained symbol-volume counter directly.
There are no padding rows and no row-count product to reconstruct. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s L : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def symbolReplicaPublicationStep
    (control savedControl gap window src dst acc trash tmp volume outAcc : Fin T) : Pr P T Q A U :=
  .seq (scatterBatch control savedControl gap window src dst acc trash tmp)
    (transfer volume dst outAcc tmp)

theorem symbolReplicaPublicationStep_exec
    (control savedControl gap window src dst acc trash tmp volume outAcc : Fin T)
    (hreg : [control,savedControl,gap,window,src,dst,acc,trash,tmp,volume,outAcc].Nodup)
    (windows : PublicationWindows s L) (w : ℕ)
    (r : PublicationReplica A) (hr : r.Valid windows w 0)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = r.input w++sourceTail) (hdst : S.R dst = r.ambient++outputTail)
    (hvolume : (S.R volume).length = s*w)
    (hc : S.R control = gatherControls A (windows.gaps w)) (hw : (S.R window).length = L*w)
    (hclean : ∀ i ∈ [savedControl,gap,acc,trash,tmp], S.R i = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (symbolReplicaPublicationStep control savedControl gap window src dst acc trash tmp volume outAcc)
        (mk v S) (windows.cost w+(4*(s*w)+4))
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R src sourceTail)
          dst outputTail) outAcc ((r.output windows w).reverse++S.R outAcc))}) := by
  have hregs := hreg
  regs_ne hregs
  have hinput : r.input w = r.words w := by
    have hh := hr.realRows
    simp only [Nat.zero_mul,List.drop_zero] at hh
    exact congrArg (cstream A w) hh
  obtain ⟨v₁,hu₁,he₁⟩ := windowScatter_exec (body := body)
    (control := control) (savedControl := savedControl) (gap := gap) (window := window)
    (src := src) (dst := dst) (acc := acc) (trash := trash) (tmp := tmp) (by regs_nodup)
    windows w r.ambient (r.words w) sourceTail outputTail hr.ambientLength hr.words_length
    v S hc hdst (by rw [←hinput]; exact hsrc) hw hclean
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R src sourceTail)
    dst (r.output windows w++outputTail))}
  have hoff (i : Fin T) (his : i ≠ src) (hid : i ≠ dst) : M.R i = S.R i := by simp [M,his,hid]
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body)
    (count := volume) (src := dst) (dst := outAcc) (tmp := tmp) (by regs_nodup)
    v₁ M (r.output windows w) outputTail (by simp [M])
    (by rw [hoff volume ‹src ≠ volume›.symm ‹dst ≠ volume›.symm,hvolume,hr.output_length])
    (by rw [hoff tmp ‹src ≠ tmp›.symm ‹dst ≠ tmp›.symm]; exact hclean _ (by simp))
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ ?_⟩
  · rw [hr.output_length]
  · apply congrArg (mk v₂)
    ext1
    · rfl
    · rfl
    · rfl
    · funext i
      simp [M,Function.update_apply,PublicationReplica.output]
      split_ifs <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
