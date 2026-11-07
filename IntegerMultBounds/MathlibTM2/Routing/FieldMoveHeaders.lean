module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHalfCount
public import IntegerMultBounds.MathlibTM2.Fast.Input

/-! Runtime dimension changes for short-field binary passes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.FieldMoveHeaders
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Replace an even unary header by its half, restoring both private tapes. -/
def halveHeader (count half saved : Fin T) : Pr P T Q A U :=
  .seq (halfCount count saved half) (.seq (uclear count) (moveR half count id))

theorem halveHeader_exec (count half saved : Fin T) (hreg : [count,half,saved].Nodup)
    (m : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hlen : (S.R count).length = 2*m) (hhalf : S.R half = []) (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧ Exec body (halveHeader count half saved) (mk v S) (12*m+8)
      (mk v' {S with R := Function.update S.R count (List.replicate m tick)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := halfCount_exec (body := body) (count := count) (saved := saved) (dst := half) (by regs_nodup) m v S hlen hsaved
  let S₁ : Stacks T A := {S with R := Function.update S.R half (List.replicate m tick)}
  have he₁' : Exec body (halfCount count saved half) (mk v S) (6*m+4) (mk v₁ S₁) := by
    simpa only [hhalf,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec (body := body) count v₁ S₁
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R count []}
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body half count ‹count ≠ half›.symm id v₂ S₂
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁' (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp [S₂,S₁,‹count ≠ half›,‹count ≠ half›.symm,hlen]; omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hic : i = count
    · subst i; simp [S₂,S₁,movedR,‹count ≠ half›.symm]
    by_cases hih : i = half
    · subst i; simp [movedR,‹count ≠ half›.symm,hhalf]
    · simp [S₂,S₁,movedR,hic,hih]

/-- Duplicate a prefix-count header, retaining its existing symbols. -/
def doubleHeader (count saved tmp : Fin T) : Pr P T Q A U :=
  .seq (copyR count saved tmp id) (moveR saved count id)

theorem doubleHeader_exec (count saved tmp : Fin T) (hreg : [count,saved,tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧ Exec body (doubleHeader count saved tmp) (mk v S)
      (6*(S.R count).length+6)
      (mk v' {S with R := Function.update S.R count (S.R count++S.R count)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := copyR_exec (body := body) count saved tmp
    ‹count ≠ saved› ‹count ≠ tmp› ‹saved ≠ tmp› id v S htmp
  let M : Stacks T A := {S with R := Function.update S.R saved (S.R count).reverse}
  have he₁' : Exec body (copyR count saved tmp id) (mk v S) (4*(S.R count).length+4) (mk v₁ M) := by
    simpa only [List.map_id,hsaved,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body saved count ‹count ≠ saved›.symm id v₁ M
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' he₂).cast ?_ ?_⟩
  · simp only [M,Function.update_self,List.length_reverse]; omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hic : i = count
    · subst i; simp [M,movedR,‹count ≠ saved›]
    by_cases his : i = saved
    · subst i; simp [movedR,‹count ≠ saved›.symm,hsaved]
    · simp [M,movedR,hic,his]

end IntegerMultBounds.MathlibTM2.Routing.FieldMoveHeaders
