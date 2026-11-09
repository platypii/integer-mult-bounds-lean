module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerIteration
public import IntegerMultBounds.MathlibTM2.Host.BankGrowth
import Mathlib.Tactic.FinCases

/-! Replacing a fixed-length column retains its volume; only the iteration header grows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main

theorem iteratedColumn_stock_eq {Q A w : ℕ} {U : Type}
    (v v' : HS 117 Q A U) (S : Stacks 117 A) (xs ys : List GaussianInt)
    (tailX : List (Fin (A+4))) (hx : S.R 110 = cstream A w xs++tailX)
    (hlen : xs.length = ys.length) :
    mnSize (mk v' (iteratedColumn S w ys tailX)) = mnSize (mk v S)+1 := by
  let roles : Fin 2 → Fin 117 := ![110,116]
  let words : Fin 2 → List (Fin (A+4)) := ![cstream A w ys++tailX,tick::S.R 116]
  have hb := mn_replace_bank_size roles (by decide : Function.Injective roles)
    v v' S (iteratedColumn S w ys tailX) words
    (by intro i; fin_cases i <;> simp [iteratedColumn,roles,words])
    (by
      intro k hk
      have h110 : k ≠ 110 := (hk 0).symm
      have h116 : k ≠ 116 := (hk 1).symm
      simp [iteratedColumn,h110,h116]) rfl rfl rfl
  simp [roles,words,Fin.sum_univ_succ,hx,hlen] at hb
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
