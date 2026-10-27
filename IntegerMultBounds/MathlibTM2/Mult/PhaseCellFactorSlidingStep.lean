module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorRow

/-! Emit the shifted row required by the next factorization update. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def factorSlidingStep : Pr P 154 Q A U :=
  .seq (.act (dropTop 107 .done)) (.seq (ucopy 107 108 135)
    (.seq (ucopy 94 108 135) (.seq factorRow (uclear 108))))

def factorSlidingStepCost (q W N n : ℕ) : ℕ :=
  1+((4*n+4)+((4*W+4)+(factorRowCost q W N n (W+n)+(2*(W+n)+2))))

theorem factorSlidingStep_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W n : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat (2*q+8) columns) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hW : (S.R 94).length = W) (hN : (S.R 116).length = B.card)
    (hcolumn : (S.R 107).length = n+1) (hrow : S.R 108 = [])
    (h105 : S.R 105 = []) (h106 : S.R 106 = [])
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail) (h0 : S.R 0 = [])
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ factorSlidingStepCost q W B.card n ∧
      Exec body factorSlidingStep (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update S.R 107 (S.R 107).tail) 140
          (cstream A (2*q+8) ((List.range' n (2*W+1)).map (fun k => factorRankWord B W columns k (W+n)))++S.R 140))}) := by
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 107 (S.R 107).tail}
  have he₁ : Exec body (.act (dropTop 107 .done)) (mk v S) 1 (mk v S₁) := by
    simpa [S₁,dropTop,Action.run,update_rt] using Exec.act (body := body) (dropTop 107 .done) (mk v S)
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec body (a := 107) (b := 108) (t := 135)
    (by decide) (by decide) (by decide) v S₁ (by simpa [S₁] using hfresh 135 (by simp))
  let S₂ : Stacks 154 A := {S₁ with R := Function.update S₁.R 108 (List.replicate n tick)}
  have he₂' : Exec body (ucopy 107 108 135) (mk v S₁) (4*n+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hcolumn,hrow] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := ucopy_exec body (a := 94) (b := 108) (t := 135)
    (by decide) (by decide) (by decide) v₂ S₂ (by simpa [S₂,S₁] using hfresh 135 (by simp))
  let S₃ : Stacks 154 A := {S₂ with R := Function.update S₂.R 108 (List.replicate (W+n) tick)}
  have he₃' : Exec body (ucopy 94 108 135) (mk v₂ S₂) (4*W+4) (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,hW,List.replicate_append_replicate] using he₃
  obtain ⟨v₄,steps,hu₄,hs,he₄⟩ := factorRow_exec (body := body) B q W n (W+n) columns hlen hformat hA tail v₃ S₃
    (by simpa [S₃,S₂,S₁] using hq) (by simpa [S₃,S₂,S₁] using hW) (by simpa [S₃,S₂,S₁] using hN)
    (by simp [S₃,S₂,S₁,hcolumn]) (by simp [S₃]) (by simpa [S₃,S₂,S₁] using hsource)
    (by simpa [S₃,S₂,S₁] using h0) (by simpa [S₃,S₂,S₁] using h105) (by simpa [S₃,S₂,S₁] using h106)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [S₃,S₂,S₁] using hfresh _ (by simp)) (by
      intro r hr1 hr7
      have hr107 : r ≠ 107 := by omega
      have hr108 : r ≠ 108 := by omega
      simpa [S₃,S₂,S₁,hr107,hr108] using hblank r hr1 hr7)
  let output := cstream A (2*q+8) ((List.range' n (2*W+1)).map (fun k => factorRankWord B W columns k (W+n)))++S.R 140
  let S₄ : Stacks 154 A := {S₃ with R := Function.update S₃.R 140 output}
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec body 108 v₄ S₄
  have h108 : (S₄.R 108).length = W+n := by simp [S₄,S₃]
  refine ⟨v₅,1+((4*n+4)+((4*W+4)+(steps+(2*(W+n)+2)))),hu₅.trans (hu₄.trans (hu₃.trans hu₂)),?_,?_⟩
  · exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_right hs _) _) _) _
  · apply (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄ he₅)))).cast (by rw [h108])
    apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk107 : k = 107 <;> by_cases hk108 : k = 108 <;> by_cases hk140 : k = 140 <;>
      simp [S₄,S₃,S₂,S₁,output,hk107,hk108,hk140,hrow]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
