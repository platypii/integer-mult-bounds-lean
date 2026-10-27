module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorWindow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorPageValues

/-! Execute the full initial-window and shifted-row factor input page from the packed table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def factorPage : Pr P 154 Q A U := .seq factorInputs factorWindow

def factorPageCost (q W N : ℕ) : ℕ := factorInputsCost q W N+factorWindowCost q W N

theorem factorPage_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat (2*q+8) columns) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hW : (S.R 94).length = W) (hN : (S.R 116).length = B.card)
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail) (h0 : S.R 0 = [])
    (hcontrols : ∀ k ∈ [(105 : Fin 154),106,107,108,111,112], S.R k = [])
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ factorPageCost q W B.card ∧
      Exec body factorPage (mk v S) steps
        (mk v' {S with R := (Function.update S.R 140
          (cstream A (2*q+8) ((factorWindowValues B W columns).flatten++
            (factorInputValues B W B.card columns).flatten)++S.R 140))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := factorInputs_exec (body := body) B q W columns hlen hformat hA tail v S
    hq hW hN (hcontrols 108 (by simp)) (hcontrols 107 (by simp))
    (hcontrols 105 (by simp)) (hcontrols 106 (by simp)) hsource h0
    (hcontrols 111 (by simp)) (hcontrols 112 (by simp)) hfresh hblank
  let S₁ : Stacks 154 A := {S with R := (Function.update S.R 140
    (cstream A (2*q+8) ((factorInputValues B W B.card columns).flatten)++S.R 140))}
  have he₁' : Exec body factorInputs (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁,factorInputValues,factorRowValues,List.flatMap] using he₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := factorWindow_exec (body := body) B q W columns hlen hformat hA tail v₁ S₁
    (by simpa [S₁] using hq) (by simpa [S₁] using hW) (by simpa [S₁] using hN)
    (by simpa [S₁] using hcontrols 107 (by simp)) (by simpa [S₁] using hcontrols 108 (by simp))
    (by simpa [S₁] using hcontrols 105 (by simp)) (by simpa [S₁] using hcontrols 106 (by simp))
    (by simpa [S₁] using hsource) (by simpa [S₁] using h0)
    (by simpa [S₁] using hcontrols 111 (by simp)) (by simpa [S₁] using hcontrols 112 (by simp))
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp)) (by
      intro r hr1 hr7
      have hr140 : r ≠ 140 := by omega
      simpa [S₁,hr140] using hblank r hr1 hr7)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,?_⟩
  simpa [factorPage,S₁,factorWindowValues,factorRowValues,List.flatMap,cstream_append,List.append_assoc]
    using Exec.seq he₁' he₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
