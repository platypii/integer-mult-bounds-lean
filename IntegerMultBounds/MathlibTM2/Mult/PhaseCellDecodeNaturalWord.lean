module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalOriginPackets
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Consume an owned real coordinate word into a unary header. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def decodeNaturalWord (src dst work saved tmp : Fin T) : Pr P T Q A U :=
  .seq (moveR src tmp id) (.seq (moveR tmp src (fun sym => bitSymbol (pairRe sym)))
    (.seq (toUnary src dst work saved tmp) (uclear src)))

theorem decodeNaturalWord_exec {src dst work saved tmp : Fin T}
    (hreg : [src,dst,work,saved,tmp].Nodup) (hA : 4 ≤ A) (w x : ℕ) (hx : x < 2^w)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = tblPairs A w x 0)
    (hfresh : ∀ k ∈ [work,saved,tmp], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 6*x+17*w+12 ∧
      Exec body (decodeNaturalWord src dst work saved tmp) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R src []) dst
          (List.replicate x tick++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  have hlen : (tblPairs A w x 0).length = w := by simp [tblPairs,coeffSyms]
  obtain ⟨v₁,hu₁,he₁⟩ := moveR_exec body src tmp ‹src ≠ tmp› id v S
  let S₁ : Stacks T A := {S with R := Function.update (Function.update S.R src []) tmp (tblPairs A w x 0).reverse}
  have he₁' : Exec body (moveR src tmp id) (mk v S) (2*w+2) (mk v₁ S₁) := by
    simpa [S₁,movedR,hsrc,hfresh tmp (by simp),hlen] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body tmp src ‹src ≠ tmp›.symm (fun sym => bitSymbol (pairRe sym)) v₁ S₁
  let S₂ : Stacks T A := {S with R := Function.update S.R src (binSyms w x)}
  have he₂' : Exec body (moveR tmp src (fun sym => bitSymbol (pairRe sym)))
      (mk v₁ S₁) (2*w+2) (mk v₂ S₂) := by
    have hh := he₂
    simp only [S₁,Function.update_self,List.length_reverse,hlen] at hh
    convert hh using 1
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hs : k = src <;> by_cases ht : k = tmp <;>
      simp_all [S₂,S₁,movedR,Function.update_apply,List.map_reverse,tblPairs_real_bits hA hx,
        hfresh tmp (by simp)]
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := toUnary_exec_linear body hreg hx v₂ S₂
    (by simp [S₂])
    (by simpa [S₂,‹src ≠ work›.symm] using hfresh work (by simp))
    (by simpa [S₂,‹src ≠ saved›.symm] using hfresh saved (by simp))
    (by simpa [S₂,‹src ≠ tmp›.symm] using hfresh tmp (by simp))
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R dst (List.replicate x tick++S.R dst)}
  have he₃' : Exec body (toUnary src dst work saved tmp) (mk v₂ S₂) m₃ (mk v₃ S₃) := by
    simpa [S₃,S₂,‹src ≠ dst›.symm] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec body src v₃ S₃
  have hlength : (S₃.R src).length = w := by simp [S₃,S₂,‹src ≠ dst›,binSyms]
  refine ⟨v₄,(2*w+2)+((2*w+2)+(m₃+(2*w+2))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),by omega,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄))).cast (by rw [hlength]) ?_⟩
  congr 1
  dsimp only [S₃,S₂]
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hs : k = src <;> by_cases hd : k = dst <;>
    simp_all [S₃,S₂,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
