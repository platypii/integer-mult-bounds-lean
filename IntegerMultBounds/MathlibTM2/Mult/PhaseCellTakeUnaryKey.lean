module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Consume one binary key into a retained unary header on arbitrary registers.
The remaining packet queue, width and every conversion scratch stack are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def takeUnaryKey (width src dst word work saved tmp : Fin T) : Pr P T Q A U :=
  .seq (takePrefix width src word work saved) (.seq (toUnary word dst work saved tmp) (uclear word))

theorem takeUnaryKey_exec {width src dst word work saved tmp : Fin T}
    (hreg : [width,src,dst,word,work,saved,tmp].Nodup) (V L : ℕ) (hL : L < 2^V)
    (suffix : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hV : (S.R width).length = V) (hsrc : S.R src = binSyms V L ++ suffix)
    (hfresh : ∀ k ∈ [dst,word,work,saved,tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 6*L+19*V+14 ∧
      Exec body (takeUnaryKey width src dst word work saved tmp) (mk v S) n
        (mk v' { S with R := (Function.update (Function.update S.R src suffix) dst (List.replicate L tick)) }) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁, hu₁, he₁⟩ := takePrefix_exec (body := body)
    (show [width,src,word,work,saved].Nodup by regs_nodup) v S (binSyms V L) suffix hsrc
    (by simpa [binSyms] using hV) (hfresh work (by simp)) (hfresh saved (by simp))
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update S.R src suffix) word (binSyms V L)) }
  have he₁' : Exec body (takePrefix width src word work saved) (mk v S) (6*V+6) (mk v₁ S₁) := by
    simpa [S₁, hfresh word (by simp), binSyms] using he₁
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := toUnary_exec_linear body
    (show [word,dst,work,saved,tmp].Nodup by regs_nodup) hL v₁ S₁ (by simp [S₁])
    (by simpa [S₁, ‹src ≠ work›.symm, ‹word ≠ work›.symm] using hfresh work (by simp))
    (by simpa [S₁, ‹src ≠ saved›.symm, ‹word ≠ saved›.symm] using hfresh saved (by simp))
    (by simpa [S₁, ‹src ≠ tmp›.symm, ‹word ≠ tmp›.symm] using hfresh tmp (by simp))
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (List.replicate L tick) }
  have he₂' : Exec body (toUnary word dst work saved tmp) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa [S₂, S₁, ‹src ≠ dst›.symm, ‹dst ≠ word›, hfresh dst (by simp)] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body word v₂ S₂
  have hlen : (S₂.R word).length = V := by simp [S₂, S₁, ‹dst ≠ word›.symm, binSyms]
  refine ⟨v₃, (6*V+6)+(n₂+(2*V+2)), hu₃.trans (hu₂.trans hu₁), by omega,
    (Exec.seq he₁' (Exec.seq he₂' he₃)).cast (by rw [hlen]) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hword : k = word
    · subst k; simp [‹src ≠ word›.symm, ‹dst ≠ word›.symm, hfresh word (by simp)]
    simp [S₂, S₁, Function.update_apply, hword]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
