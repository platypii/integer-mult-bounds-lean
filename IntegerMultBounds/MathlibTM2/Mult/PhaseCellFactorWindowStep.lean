module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorRow

/-! Descend the row cursor and prepend one complete start-zero window row. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def factorWindowStep : Pr P 154 Q A U := .seq (.act (dropTop 108 .done)) factorRow

theorem factorWindowStep_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W m : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat (2*q+8) columns) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hW : (S.R 94).length = W) (hN : (S.R 116).length = B.card)
    (hcolumn : S.R 107 = []) (hrow : (S.R 108).length = m+1)
    (h105 : S.R 105 = []) (h106 : S.R 106 = [])
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail) (h0 : S.R 0 = [])
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ 1+factorRowCost q W B.card 0 m ∧
      Exec body factorWindowStep (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update S.R 108 (S.R 108).tail) 140
          (cstream A (2*q+8) ((List.range' 0 (2*W+1)).map (fun n => factorRankWord B W columns n m))++S.R 140))}) := by
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 108 (S.R 108).tail}
  have he₁ : Exec body (.act (dropTop 108 .done)) (mk v S) 1 (mk v S₁) := by
    simpa [S₁,dropTop,Action.run,update_rt] using Exec.act (body := body) (dropTop 108 .done) (mk v S)
  obtain ⟨v',steps,hu,hs,he⟩ := factorRow_exec (body := body) B q W 0 m columns hlen hformat hA tail v S₁
    (by simpa [S₁] using hq) (by simpa [S₁] using hW) (by simpa [S₁] using hN)
    (by simp [S₁,hcolumn]) (by simp [S₁,hrow]) (by simpa [S₁] using hsource) (by simpa [S₁] using h0) (by simpa [S₁] using h105) (by simpa [S₁] using h106)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp)) (by
      intro r hr1 hr7
      have hr108 : r ≠ 108 := by omega
      simpa [S₁,hr108] using hblank r hr1 hr7)
  refine ⟨v',1+steps,hu,Nat.add_le_add_left hs 1,?_⟩
  simpa [factorWindowStep,S₁] using Exec.seq he₁ he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
