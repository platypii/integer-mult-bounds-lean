module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFetchPage

/-! # Fetch the final table behind the two generator banks and scalar -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def fetchOutputTable : Pr P 117 Q A U := fetchPage 2

def fetchOutputTableCost (M L w : ℕ) : ℕ := fetchPageCost 2 M L w

theorem fetchOutputTable_exec (M L w : ℕ) (pre table tail : List (Fin (A + 4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hbatch : (S.R 108).length = 2 * M) (hrows : (S.R 103).length = L) (hwidth : (S.R 94).length = w)
    (hpre : pre.length = 2 * (M * L * w) + w) (htable : table.length = M * L * w)
    (hsrc : S.R 110 = pre ++ (table ++ tail))
    (hclean : ∀ k ∈ [(1 : Fin 117), 2, 3, 7, 8, 26, 27, 96, 112], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ fetchOutputTableCost M L w ∧
      Exec body fetchOutputTable (mk v S) m
        (mk v' { S with R := Function.update S.R 96 table }) := by
  simpa only [fetchOutputTable, fetchOutputTableCost] using
    fetchPage_exec (body := body) 2 M L w pre table tail v S hbatch hrows hwidth hpre htable hsrc hclean

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
