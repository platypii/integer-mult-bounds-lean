module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDecodeNaturalWord

/-! Consume one encoded coordinate into unary without a scaled binary workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def takeNaturalCoordinate (width src dst word work saved tmp : Fin T) : Pr P T Q A U :=
  .seq (takePrefix width src word work saved) (decodeNaturalWord word dst work saved tmp)

/-- Only the source prefix is consumed and the unary coordinate is appended;
coordinate width, borrowed suffix and every conversion scratch tape restore. -/
theorem takeNaturalCoordinate_exec {width src dst word work saved tmp : Fin T}
    (hreg : [width,src,dst,word,work,saved,tmp].Nodup) (hA : 4 ≤ A)
    (V x : ℕ) (hx : x < 2^V) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A) (hwidth : (S.R width).length = V)
    (hsrc : S.R src = tblPairs A V x 0++tail)
    (hclean : ∀ i ∈ [word,work,saved,tmp], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 6*x+23*V+18 ∧
      Exec body (takeNaturalCoordinate width src dst word work saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src tail) dst
          (List.replicate x tick++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := takePrefix_exec (body := body)
    (count := width) (src := src) (dst := word) (buf := work) (tmp := saved)
    (by regs_nodup) v S (tblPairs A V x 0) tail hsrc
    (by simpa [tblPairs,coeffSyms] using hwidth)
    (hclean work (by simp)) (hclean saved (by simp))
  let S₁ : Stacks T A := {S with R := (Function.update (Function.update S.R src tail) word (tblPairs A V x 0))}
  have he₁' : Exec body (takePrefix width src word work saved) (mk v S) (6*V+6) (mk v₁ S₁) := by
    simpa [S₁,tblPairs,coeffSyms,hclean word (by simp)] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := decodeNaturalWord_exec (body := body)
    (src := word) (dst := dst) (work := work) (saved := saved) (tmp := tmp)
    (by regs_nodup) hA V x hx v₁ S₁ (by simp [S₁]) (by
      intro i hi
      have ho : i ≠ src ∧ i ≠ word := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl <;> constructor <;> first | assumption | exact Ne.symm (by assumption)
      simpa [S₁,ho.1,ho.2] using hclean i (by simp_all))
  refine ⟨v₂,(6*V+6)+n₂,hu₂.trans hu₁,by omega,(Exec.seq he₁' he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hsrc' : i = src <;> by_cases hdst : i = dst <;> by_cases hword : i = word <;>
    simp_all [S₁]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
