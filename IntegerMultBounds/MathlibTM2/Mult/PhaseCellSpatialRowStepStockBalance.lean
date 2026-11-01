module

public import IntegerMultBounds.MathlibTM2.Host.ExchangeFourStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedSpatialRowStepStock

/-! Guard consumption pays for the coordinate tick; all three word transfers
exchange equally sized prefixes. A complete spatial step preserves endpoint stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
variable {Q A : ℕ} {U : Type}

theorem spatialRowStep_stock (v w : HS 144 Q A U) (S : Stacks 144 A)
    (width : ℕ) (guard : Fin (A+4)) (coeffs source : List GaussianInt)
    (j : ℕ) (hj : j < source.length) (rhs z : GaussianInt)
    (maskTail pageTail rhsTail tail : List (Fin (A+4)))
    (hmask : S.R 136 = guard::maskTail)
    (hpage : S.R 138 = cstream A width coeffs++pageTail)
    (hrhs : S.R 93 = csyms A width rhs++rhsTail)
    (hsource : S.R 141 = cstream A width (source.drop j)++tail) :
    mnSize (mk w {S with R := (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update S.R 136 maskTail) 138 pageTail) 137
        ((cstream A width coeffs).reverse++S.R 137)) 113 (csyms A width z++S.R 113))
      93 rhsTail) 141 (cstream A width (source.drop (j+1))++tail))
      142 ((csyms A width (source[j]'hj)).reverse++S.R 142)) 107 (tick::S.R 107))}) =
      mnSize (mk v S) := by
  let r : Fin 8 → Fin 144 := ![136,138,93,141,107,137,113,142]
  have hr : Function.Injective r := by decide +kernel
  let xs : Fin 4 → List (Fin (A+4)) :=
    ![[guard],cstream A width coeffs,csyms A width rhs,csyms A width (source[j]'hj)]
  let us : Fin 4 → List (Fin (A+4)) :=
    ![[tick],(cstream A width coeffs).reverse,csyms A width z,(csyms A width (source[j]'hj)).reverse]
  let tails : Fin 4 → List (Fin (A+4)) :=
    ![maskTail,pageTail,rhsTail,cstream A width (source.drop (j+1))++tail]
  have h := mn_exchange_four_size r hr v w S xs us tails (by
    intro i
    fin_cases i
    · exact hmask
    · exact hpage
    · exact hrhs
    · change S.R 141 = csyms A width (source[j]'hj)++(cstream A width (source.drop (j+1))++tail)
      rw [hsource,List.drop_eq_getElem_cons hj,cstream_cons,List.append_assoc]) (by
    intro i
    fin_cases i <;> simp [us,xs,csyms])
  let M : Stacks 144 A := {S with R := (Function.update (Function.update (Function.update
    (Function.update S.R 136 maskTail) 138 pageTail) 107 (tick::S.R 107))
    137 ((cstream A width coeffs).reverse++S.R 137))}
  let F : Stacks 144 A := {M with R := (Function.update (Function.update (Function.update
    (Function.update M.R 93 rhsTail) 141 (cstream A width (source.drop (j+1))++tail))
    113 (csyms A width z++M.R 113)) 142 ((csyms A width (source[j]'hj)).reverse++M.R 142))}
  change mnSize (mk w F) = mnSize (mk v S) at h
  have hF : F = {S with R := (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update S.R 136 maskTail) 138 pageTail) 137
        ((cstream A width coeffs).reverse++S.R 137)) 113 (csyms A width z++S.R 113))
      93 rhsTail) 141 (cstream A width (source.drop (j+1))++tail))
      142 ((csyms A width (source[j]'hj)).reverse++S.R 142)) 107 (tick::S.R 107))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h136 : k = 136
    · subst k; simp [F,M]
    by_cases h138 : k = 138
    · subst k; simp [F,M]
    by_cases h107 : k = 107
    · subst k; simp [F,M]
    by_cases h137 : k = 137
    · subst k; simp [F,M]
    by_cases h93 : k = 93
    · subst k; simp [F,M]
    by_cases h141 : k = 141
    · subst k; simp [F,M]
    by_cases h113 : k = 113
    · subst k; simp [F,M]
    by_cases h142 : k = 142
    · subst k; simp [F,M]
    simp [F,M,h136,h138,h107,h137,h93,h141,h113,h142]
  rw [hF] at h
  exact h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
