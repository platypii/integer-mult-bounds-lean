module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorWord

/-! Descend the column cursor before emitting one row word, so stack accumulation has natural row order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def factorInputRowStep : Pr P 154 Q A U := .seq (.act (dropTop 107 .done)) factorWord

theorem factorInputRowStep_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W n m : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat (2*q+8) columns) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hW : (S.R 94).length = W) (hN : (S.R 116).length = B.card)
    (hcolumn : (S.R 107).length = n+1) (hrow : (S.R 108).length = m)
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail) (h0 : S.R 0 = [])
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ 1+factorWordCost q n m W B.card ∧
      Exec body factorInputRowStep (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update S.R 107 (S.R 107).tail) 140
          (csyms A (2*q+8) (factorRankWord B W columns n m)++S.R 140))}) := by
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 107 (S.R 107).tail}
  have he₁ : Exec body (.act (dropTop 107 .done)) (mk v S) 1 (mk v S₁) := by
    simpa [S₁,dropTop,Action.run,update_rt] using Exec.act (body := body) (dropTop 107 .done) (mk v S)
  obtain ⟨v',steps,hu,hs,he⟩ := factorWord_exec (body := body) B q W n m columns hlen hformat hA tail v S₁
    (by simpa [S₁] using hq) (by simpa [S₁] using hW) (by simpa [S₁] using hN)
    (by simp [S₁,hcolumn]) (by simpa [S₁] using hrow) (by simpa [S₁] using hsource) (by simpa [S₁] using h0)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp)) (by
      intro r hr1 hr7
      have hr107 : r ≠ 107 := by omega
      simpa [S₁,hr107] using hblank r hr1 hr7)
  refine ⟨v',1+steps,hu,Nat.add_le_add_left hs 1,?_⟩
  simpa [factorInputRowStep,S₁] using Exec.seq he₁ he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
