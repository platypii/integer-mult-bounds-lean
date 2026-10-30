module

public import IntegerMultBounds.MathlibTM2.Fast.Input
public import IntegerMultBounds.MathlibTM2.Layer.Format

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Restoring mapped copy in the original symbol order. -/
def copyMappedWords (src dst tmp saved : Fin T) (f : Fin (A+4) → Fin (A+4)) : Pr P T Q A U :=
  .seq (copyR src tmp saved f) (moveR tmp dst id)

theorem copyMappedWords_exec (src dst tmp saved : Fin T)
    (hreg : [src,dst,tmp,saved].Nodup) (f : Fin (A+4) → Fin (A+4))
    (v : HS T Q A U) (S : Stacks T A) (htmp : S.R tmp = []) (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copyMappedWords src dst tmp saved f) (mk v S) (6*(S.R src).length+6)
        (mk v' {S with R := Function.update S.R dst ((S.R src).map f++S.R dst)}) := by
  have hr := hreg
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  rcases hr with ⟨⟨hsd,hst,hss⟩,⟨⟨hdt,hds⟩,⟨hts,_⟩⟩⟩
  obtain ⟨v₁,hu₁,he₁⟩ := copyR_exec body src tmp saved ‹src ≠ tmp› ‹src ≠ saved› ‹tmp ≠ saved› f v S hsaved
  let M : Stacks T A := {S with R := Function.update S.R tmp ((S.R src).map f).reverse}
  have he₁' : Exec body (copyR src tmp saved f) (mk v S) (4*(S.R src).length+4) (mk v₁ M) := by
    simpa only [htmp,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body tmp dst ‹dst ≠ tmp›.symm id v₁ M
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' he₂).cast ?_ ?_⟩
  · simp [M,List.length_reverse,List.length_map]; omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hd : i = dst
    · subst i; simp [M,movedR,‹dst ≠ tmp›]
    by_cases ht : i = tmp
    · subst i; simp [M,movedR,hd,htmp]
    · simp [M,movedR,hd,ht]

def pairRealBit {A : ℕ} (x : Fin (A+4)) : Fin (A+4) := bitSymbol (pairRe x)
def pairImagBit {A : ℕ} (x : Fin (A+4)) : Fin (A+4) := bitSymbol (pairIm x)

/-- Two bit planes avoid any expansion by the ambient alphabet size. -/
def copyPairBitPlanes (src re im tmp saved : Fin T) : Pr P T Q A U :=
  .seq (copyMappedWords src re tmp saved pairRealBit) (copyMappedWords src im tmp saved pairImagBit)

theorem copyPairBitPlanes_exec (src re im tmp saved : Fin T)
    (hreg : [src,re,im,tmp,saved].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (htmp : S.R tmp = []) (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copyPairBitPlanes src re im tmp saved) (mk v S) (12*(S.R src).length+12)
        (mk v' {S with R := (Function.update (Function.update S.R re
          ((S.R src).map pairRealBit++S.R re)) im ((S.R src).map pairImagBit++S.R im))}) := by
  have hr := hreg
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  rcases hr with ⟨⟨hsr,hsi,hst,hss⟩,⟨⟨hri,hrt,hrs⟩,⟨⟨hit,his⟩,⟨hts,_⟩⟩⟩⟩
  obtain ⟨v₁,hu₁,he₁⟩ := copyMappedWords_exec src re tmp saved (by simp_all) pairRealBit v S htmp hsaved
  let M : Stacks T A := {S with R := Function.update S.R re ((S.R src).map pairRealBit++S.R re)}
  obtain ⟨v₂,hu₂,he₂⟩ := copyMappedWords_exec src im tmp saved (by simp_all) pairImagBit v₁ M
    (by simpa [M,‹re ≠ tmp›.symm] using htmp) (by simpa [M,‹re ≠ saved›.symm] using hsaved)
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ ?_⟩
  · simp [M,‹src ≠ re›]; omega
  · apply congrArg (mk v₂)
    simp [M,‹src ≠ re›,‹re ≠ im›.symm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
