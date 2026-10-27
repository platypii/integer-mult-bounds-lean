module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorPage

/-! Derive the factor half-band header from the retained band master and release it after page emission. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def factorBandWidth : Pr P 154 Q A U :=
  .seq (umul 12 124 94 135) (.act (.push (.rt 94) (fun _ => tick) .done))

theorem factorBandWidth_exec (band : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hband : (S.R 124).length = band) (h94 : S.R 94 = []) (h135 : S.R 135 = []) :
    ∃ v', v'.user = v.user ∧ Exec body factorBandWidth (mk v S) (4*band+5)
      (mk v' {S with R := Function.update S.R 94 (List.replicate (12*band+1) tick)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := umul_exec body 12 (a := 124) (b := 94) (t := 135) (by decide) (by decide) (by decide) v S h135
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 94 (List.replicate (12*band) tick)}
  have he₁' : Exec body (umul 12 124 94 135) (mk v S) (4*band+4) (mk v₁ S₁) := by
    simpa [S₁,hband,h94] using he₁
  have he₂ := Exec.act (body := body) (.push (.rt 94) (fun _ => tick) .done) (mk v₁ S₁)
  refine ⟨v₁,hu₁,(Exec.seq he₁' he₂).cast (by omega) ?_⟩
  simp [S₁,Action.run,update_rt,List.replicate_succ]

def generatedFactorPage : Pr P 154 Q A U := .seq factorBandWidth (.seq factorPage (uclear 94))

def generatedFactorPageCost (q band N : ℕ) : ℕ :=
  (4*band+5)+(factorPageCost q (12*band+1) N+(2*(12*band+1)+2))

theorem generatedFactorPage_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q band : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat (2*q+8) columns) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hband : (S.R 124).length = band) (hN : (S.R 116).length = B.card)
    (hsource : S.R 132 = bandTableWords A (2*q+8) B (12*band+1) columns 0++tail)
    (h0 : S.R 0 = []) (h94 : S.R 94 = [])
    (hcontrols : ∀ k ∈ [(105 : Fin 154),106,107,108,111,112], S.R k = [])
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ generatedFactorPageCost q band B.card ∧
      Exec body generatedFactorPage (mk v S) steps
        (mk v' {S with R := (Function.update S.R 140
          (cstream A (2*q+8) ((factorWindowValues B (12*band+1) columns).flatten++
            (factorInputValues B (12*band+1) B.card columns).flatten)++S.R 140))}) := by
  let W := 12*band+1
  obtain ⟨v₁,hu₁,he₁⟩ := factorBandWidth_exec (body := body) band v S hband h94 (hfresh 135 (by simp))
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 94 (List.replicate W tick)}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := factorPage_exec (body := body) B q W columns hlen hformat hA tail v₁ S₁
    (by simpa [S₁] using hq) (by simp [S₁]) (by simpa [S₁] using hN)
    (by simpa [S₁,W] using hsource) (by simpa [S₁] using h0)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [S₁] using hcontrols _ (by simp))
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp)) (by
      intro r hr1 hr7
      have hr94 : r ≠ 94 := by omega
      simpa [S₁,hr94] using hblank r hr1 hr7)
  let output := cstream A (2*q+8) ((factorWindowValues B W columns).flatten++
    (factorInputValues B W B.card columns).flatten)++S.R 140
  let S₂ : Stacks 154 A := {S₁ with R := Function.update S₁.R 140 output}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 94 v₂ S₂
  have hlen94 : (S₂.R 94).length = W := by simp [S₂,S₁]
  refine ⟨v₃,(4*band+5)+(m₂+(2*W+2)),hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add_left (Nat.add_le_add_right hm₂ _) _,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hlen94]) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk94 : k = 94 <;> by_cases hk140 : k = 140 <;> simp [S₂,S₁,output,W,hk94,hk140,h94]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
