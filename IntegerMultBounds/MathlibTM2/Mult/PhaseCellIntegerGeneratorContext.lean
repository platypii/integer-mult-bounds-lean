module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerIteration

/-! # The retained context between integer generator iterations -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node

structure IntegerGeneratorContext {A : ℕ} (P s t u band L n w : ℕ)
    (tailX tailF : List (Fin (A + 4))) (S : Stacks 117 A) : Prop where
  row : IntegerRowContext L w (rowColumnWords P s t u band L n) tailX S
  count : (S.R 103).length = L
  precision : (S.R 114).length = P
  iteration : (S.R 116).length = n
  saved : S.R 108 = []
  factors : S.R 109 = cstream A w ((List.range L).reverse.flatMap (rowFactorWords P s t u band L)) ++ tailF
  rest : S.R 107 = []
  exponent : S.R 115 = []

theorem IntegerGeneratorContext.update {A P s t u band L n w : ℕ}
    {tailX tailF : List (Fin (A + 4))} {S : Stacks 117 A}
    (h : IntegerGeneratorContext P s t u band L n w tailX tailF S) (k : Fin 117)
    (hk : k ∈ [(100 : Fin 117), 101, 111, 113]) (zs : List (Fin (A + 4))) :
    IntegerGeneratorContext P s t u band L n w tailX tailF { S with R := Function.update S.R k zs } := by
  have hoff (j : Fin 117) (hj : j ∈ [(103 : Fin 117), 114, 116, 108, 109, 107, 115]) : j ≠ k := by
    have hd : [(103 : Fin 117), 114, 116, 108, 109, 107, 115].Disjoint [100, 101, 111, 113] := by simp
    intro he
    subst j
    exact List.disjoint_left.mp hd hj hk
  refine ⟨h.row.update k ((by decide : [(100 : Fin 117), 101, 111, 113].Sublist
    [100, 101, 103, 108, 111, 112, 113, 116]).subset hk) zs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hoff 103 (by simp)] using h.count
  · simpa [hoff 114 (by simp)] using h.precision
  · simpa [hoff 116 (by simp)] using h.iteration
  · simpa [hoff 108 (by simp)] using h.saved
  · simpa [hoff 109 (by simp)] using h.factors
  · simpa [hoff 107 (by simp)] using h.rest
  · simpa [hoff 115 (by simp)] using h.exponent

theorem IntegerGeneratorContext.next {A P s t u band L n w : ℕ}
    {tailX tailF : List (Fin (A + 4))} {S : Stacks 117 A}
    (h : IntegerGeneratorContext P s t u band L n w tailX tailF S)
    (hrow : IntegerRowContext L w (rowColumnWords P s t u band L (n + 1)) tailX
      (iteratedColumn S w (rowColumnWords P s t u band L (n + 1)) tailX)) :
    IntegerGeneratorContext P s t u band L (n + 1) w tailX tailF
      (iteratedColumn S w (rowColumnWords P s t u band L (n + 1)) tailX) := by
  refine ⟨hrow, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [iteratedColumn] using h.count
  · simpa [iteratedColumn] using h.precision
  · simp [iteratedColumn, h.iteration]
  · simpa [iteratedColumn] using h.saved
  · simpa [iteratedColumn] using h.factors
  · simpa [iteratedColumn] using h.rest
  · simpa [iteratedColumn] using h.exponent

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
