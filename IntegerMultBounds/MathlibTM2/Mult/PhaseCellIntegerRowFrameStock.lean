module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowConsume
public import IntegerMultBounds.MathlibTM2.Host.BankGrowth
import Mathlib.Tactic.FinCases

/-! Consumed row descriptors pay for the published result at scan boundaries. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main

/-- One RHS word is replaced by one output word; the owned factor row disappears. -/
theorem consumeIntegerRow_stock_le {Q A w : ℕ} {U : Type}
    (v v' : HS 117 Q A U) (S : Stacks 117 A)
    (as : List GaussianInt) (rhs result : GaussianInt)
    (tailA tailR : List (Fin (A+4)))
    (ha : S.R 111 = cstream A w as++tailA)
    (hr : S.R 112 = csyms A w rhs++tailR) :
    mnSize (mk v' {S with R := Function.update (Function.update
      (Function.update S.R 111 tailA) 112 tailR) 113 (csyms A w result++S.R 113)}) ≤
      mnSize (mk v S) := by
  let roles : Fin 3 → Fin 117 := ![111,112,113]
  let words : Fin 3 → List (Fin (A+4)) := ![tailA,tailR,csyms A w result++S.R 113]
  let F : Stacks 117 A := {S with R := Function.update (Function.update
    (Function.update S.R 111 tailA) 112 tailR) 113 (csyms A w result++S.R 113)}
  have hroles : Function.Injective roles := by decide
  have hb := mn_replace_bank_size roles hroles v v' S F words
    (by intro i; fin_cases i <;> simp [F,roles,words])
    (by
      intro k hk
      have h111 := (hk 0).symm
      have h112 := (hk 1).symm
      have h113 := (hk 2).symm
      change k ≠ 111 at h111
      change k ≠ 112 at h112
      change k ≠ 113 at h113
      simp [F,h111,h112,h113]) rfl rfl rfl
  simp [roles,words,Fin.sum_univ_succ,ha,hr] at hb
  change mnSize (mk v' F) ≤ mnSize (mk v S)
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
