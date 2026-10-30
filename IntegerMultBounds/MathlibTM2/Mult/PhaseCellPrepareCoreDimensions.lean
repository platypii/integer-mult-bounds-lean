module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Construct shared unary radius and core-length masters from binary group
geometry. Decode the halo length once, then remove its two radius margins. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def prepareCoreDimensions (radiusWord lengthWord radius rows work saved tmp : Fin T) : Pr P T Q A U :=
  .seq (toUnary radiusWord radius work saved tmp)
    (.seq (toUnary lengthWord rows work saved tmp)
      (.seq (discardPrefix radius rows work saved) (discardPrefix radius rows work saved)))

def prepareCoreDimensionsCost (V L radius : ℕ) : ℕ := 6*L+18*radius+22*V+24

theorem prepareCoreDimensions_exec {radiusWord lengthWord radius rows work saved tmp : Fin T}
    (hreg : [radiusWord,lengthWord,radius,rows,work,saved,tmp].Nodup)
    (V n r : ℕ) (hr : r < 2^V) (hL : n+2*r < 2^V)
    (v : HS T Q A U) (S : Stacks T A)
    (hradius : S.R radiusWord = binSyms V r) (hlength : S.R lengthWord = binSyms V (n+2*r))
    (hfresh : ∀ k ∈ [radius,rows,work,saved,tmp], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCoreDimensionsCost V (n+2*r) r ∧
      Exec body (prepareCoreDimensions radiusWord lengthWord radius rows work saved tmp) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R radius (List.replicate r tick))
          rows (List.replicate n tick))}) := by
  have hh := hreg
  regs_ne hh
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear body
    (a := radiusWord) (z := radius) (w := work) (t := saved) (t₂ := tmp)
    (by regs_nodup) hr v S hradius (hfresh work (by simp)) (hfresh saved (by simp)) (hfresh tmp (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R radius (List.replicate r tick)}
  have he₁' : Exec body (toUnary radiusWord radius work saved tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hfresh radius (by simp)] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := toUnary_exec_linear body
    (a := lengthWord) (z := rows) (w := work) (t := saved) (t₂ := tmp)
    (by regs_nodup) hL v₁ S₁ (by simpa [S₁,‹lengthWord ≠ radius›] using hlength)
    (by simpa [S₁,‹radius ≠ work›.symm] using hfresh work (by simp))
    (by simpa [S₁,‹radius ≠ saved›.symm] using hfresh saved (by simp))
    (by simpa [S₁,‹radius ≠ tmp›.symm] using hfresh tmp (by simp))
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R rows (List.replicate (n+2*r) tick)}
  have he₂' : Exec body (toUnary lengthWord rows work saved tmp) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,‹radius ≠ rows›.symm,hfresh rows (by simp)] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := discardPrefix_exec (body := body)
    (count := radius) (src := rows) (trash := work) (tmp := saved) (by regs_nodup)
    (List.replicate r tick) (List.replicate (n+r) tick) v₂ S₂
    (by
      simp only [S₂,Function.update_self,List.replicate_append_replicate]
      congr 1; omega)
    (by simp [S₂,S₁,‹radius ≠ rows›])
    (by simpa [S₂,S₁,‹rows ≠ work›.symm,‹radius ≠ work›.symm] using hfresh work (by simp))
    (by simpa [S₂,S₁,‹rows ≠ saved›.symm,‹radius ≠ saved›.symm] using hfresh saved (by simp))
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R rows (List.replicate (n+r) tick)}
  obtain ⟨v₄,hu₄,he₄⟩ := discardPrefix_exec (body := body)
    (count := radius) (src := rows) (trash := work) (tmp := saved) (by regs_nodup)
    (List.replicate r tick) (List.replicate n tick) v₃ S₃
    (by simp [S₃,List.replicate_append_replicate,Nat.add_comm])
    (by simp [S₃,S₂,S₁,‹radius ≠ rows›])
    (by simpa [S₃,S₂,S₁,‹rows ≠ work›.symm,‹radius ≠ work›.symm] using hfresh work (by simp))
    (by simpa [S₃,S₂,S₁,‹rows ≠ saved›.symm,‹radius ≠ saved›.symm] using hfresh saved (by simp))
  refine ⟨v₄,n₁+(n₂+((6*r+6)+(6*r+6))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄))).cast (by simp) ?_⟩
  · unfold prepareCoreDimensionsCost
    omega
  · apply congrArg (mk v₄)
    simp only [S₃,S₂,S₁,Function.update_idem]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
