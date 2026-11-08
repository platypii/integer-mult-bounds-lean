module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.StackResources

/-! One monotone halo window. Consume the previous overlap once, consume only
new source bytes, and retain the next overlap wholly within the newly read tail.
No whole-window reread or shifting overlap queue is used. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloWindowStep
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def emitWindow (bodyCount keepCount src archive oldOverlap nextOverlap saved tmp : Fin T) : Pr P T Q A U :=
  .seq (moveR oldOverlap archive id)
    (.seq (transfer bodyCount src archive tmp)
      (.seq (copyPrefix keepCount src nextOverlap saved tmp) (transfer keepCount src archive tmp)))

theorem emitWindow_exec (bodyCount keepCount src archive oldOverlap nextOverlap saved tmp : Fin T)
    (hreg : [bodyCount,keepCount,src,archive,oldOverlap,nextOverlap,saved,tmp].Nodup)
    (old fresh kept tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hbody : (S.R bodyCount).length = fresh.length) (hkeep : (S.R keepCount).length = kept.length)
    (hsrc : S.R src = fresh++kept++tail) (hold : S.R oldOverlap = old)
    (hnext : S.R nextOverlap = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ vf, vf.user = v.user ∧
      Exec body (emitWindow bodyCount keepCount src archive oldOverlap nextOverlap saved tmp) (mk v S)
        (2*old.length+4*fresh.length+14*kept.length+20)
        (mk vf {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          oldOverlap []) src tail) archive ((old++fresh++kept).reverse++S.R archive)) nextOverlap kept)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := moveR_exec body oldOverlap archive ‹archive ≠ oldOverlap›.symm id v S
  let S₁ : Stacks T A := {S with R := (Function.update (Function.update S.R oldOverlap []) archive (old.reverse++S.R archive))}
  have he₁' : Exec body (moveR oldOverlap archive id) (mk v S) (2*old.length+2) (mk v₁ S₁) := by
    simpa only [hold,movedR,List.map_id] using he₁
  have off₁ (i : Fin T) (hio : i ≠ oldOverlap) (hia : i ≠ archive) : S₁.R i = S.R i := by
    simp [S₁,hio,hia]
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body) (count := bodyCount) (src := src)
    (dst := archive) (tmp := tmp) (by regs_nodup) v₁ S₁ fresh (kept++tail)
    (by rw [off₁ src ‹src ≠ oldOverlap› ‹src ≠ archive›]; simpa only [List.append_assoc] using hsrc)
    (by rw [off₁ bodyCount ‹bodyCount ≠ oldOverlap› ‹bodyCount ≠ archive›]; exact hbody)
    (by rw [off₁ tmp ‹oldOverlap ≠ tmp›.symm ‹archive ≠ tmp›.symm]; exact htmp)
  let S₂ : Stacks T A := {S₁ with R := (Function.update (Function.update S₁.R src (kept++tail))
    archive (fresh.reverse++S₁.R archive))}
  have off₂ (i : Fin T) (his : i ≠ src) (hia : i ≠ archive) (hio : i ≠ oldOverlap) : S₂.R i = S.R i := by
    simp only [S₂,Function.update_of_ne hia,Function.update_of_ne his]; exact off₁ i hio hia
  obtain ⟨v₃,hu₃,he₃⟩ := copyPrefix_exec (body := body) (count := keepCount) (src := src)
    (dst := nextOverlap) (saved := saved) (tmp := tmp) (by regs_nodup) v₂ S₂ kept tail
    (by simp [S₂,‹src ≠ archive›])
    (by rw [off₂ keepCount ‹keepCount ≠ src› ‹keepCount ≠ archive› ‹keepCount ≠ oldOverlap›]; exact hkeep)
    (by rw [off₂ saved ‹src ≠ saved›.symm ‹archive ≠ saved›.symm ‹oldOverlap ≠ saved›.symm]; exact hsaved)
    (by rw [off₂ tmp ‹src ≠ tmp›.symm ‹archive ≠ tmp›.symm ‹oldOverlap ≠ tmp›.symm]; exact htmp)
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R nextOverlap kept}
  have he₃' : Exec body (copyPrefix keepCount src nextOverlap saved tmp) (mk v₂ S₂) (10*kept.length+10) (mk v₃ S₃) := by
    simpa only [off₂ nextOverlap ‹src ≠ nextOverlap›.symm ‹archive ≠ nextOverlap›.symm ‹oldOverlap ≠ nextOverlap›.symm,
      hnext,List.append_nil] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := transfer_exec (body := body) (count := keepCount) (src := src)
    (dst := archive) (tmp := tmp) (by regs_nodup) v₃ S₃ kept tail
    (by simp [S₃,S₂,‹src ≠ nextOverlap›,‹src ≠ archive›])
    (by simp only [S₃,Function.update_of_ne ‹keepCount ≠ nextOverlap›];
        rw [off₂ keepCount ‹keepCount ≠ src› ‹keepCount ≠ archive› ‹keepCount ≠ oldOverlap›]; exact hkeep)
    (by simp only [S₃,Function.update_of_ne ‹nextOverlap ≠ tmp›.symm];
        rw [off₂ tmp ‹src ≠ tmp›.symm ‹archive ≠ tmp›.symm ‹oldOverlap ≠ tmp›.symm]; exact htmp)
  refine ⟨v₄,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' he₄))).cast (by omega) ?_⟩
  apply congrArg (mk v₄)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hio : i = oldOverlap
  · subst i
    simp [S₃,S₂,S₁,‹src ≠ oldOverlap›.symm,‹archive ≠ oldOverlap›.symm,‹oldOverlap ≠ nextOverlap›]
  by_cases his : i = src
  · subst i
    simp [‹src ≠ archive›,‹src ≠ nextOverlap›]
  by_cases hia : i = archive
  · subst i
    simp [S₃,S₂,S₁,‹archive ≠ nextOverlap›,List.reverse_append,List.append_assoc]
  by_cases hin : i = nextOverlap
  · subst i
    simp [S₃,‹src ≠ nextOverlap›.symm,‹archive ≠ nextOverlap›.symm]
  · simp [S₃,S₂,S₁,Function.update_apply,hio,his,hia,hin]

theorem emitWindow_pushBound (bodyCount keepCount src archive oldOverlap nextOverlap saved tmp : Fin T) :
    mnNativePushBound 2 (emitWindow (P := P) (Q := Q) (A := A) (U := U)
      bodyCount keepCount src archive oldOverlap nextOverlap saved tmp) := by
  simp [emitWindow,copyPrefix,copyR,copyStep,transfer,scanR,keepIn,transferAct,drainR,popDo,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]


end IntegerMultBounds.MathlibTM2.Routing.HaloWindowStep
