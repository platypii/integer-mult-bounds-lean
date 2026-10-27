module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClippedBandControls

/-! Prepare the collector's controls from the retained geometry and folded-column index. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def residentBandWidth : Pr P 151 Q A U :=
  .seq (umul 12 124 94 135) (.act (.push (.rt 94) (fun _ => tick) .done))

theorem residentBandWidth_exec (band : ℕ) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hband : (S.R 124).length = band) (h94 : S.R 94 = []) (h135 : S.R 135 = []) :
    ∃ v', v'.user = v.user ∧ Exec body residentBandWidth (mk v S) (4*band+5)
      (mk v' {S with R := Function.update S.R 94 (List.replicate (12*band+1) tick)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := umul_exec body 12 (a := 124) (b := 94) (t := 135)
    (by decide) (by decide) (by decide) v S h135
  let S₁ : Stacks 151 A := {S with R := Function.update S.R 94 (List.replicate (12*band) tick)}
  have he₁' : Exec body (umul 12 124 94 135) (mk v S) (4*band+4) (mk v₁ S₁) := by
    simpa [S₁,hband,h94] using he₁
  have he₂ := Exec.act (body := body) (.push (.rt 94) (fun _ => tick) .done) (mk v₁ S₁)
  refine ⟨v₁,hu₁,(Exec.seq he₁' he₂).cast (by omega) ?_⟩
  simp [S₁,Action.run,update_rt,List.replicate_succ]

def residentBandControls : Pr P 151 Q A U :=
  .seq residentBandWidth (.seq (clippedBandControls 0 94 116 137 138 136 135)
    (.seq (uclear 94) (uclear 0)))

def residentBandControlsCost (n band rowCount : ℕ) : ℕ :=
  (4*band+5)+(clippedBandControlsCost n (12*band+1) rowCount+
    ((2*(12*band+1)+2)+(2*n+2)))

theorem residentBandControls_exec (n band rowCount : ℕ) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hn : (S.R 0).length = n) (hband : (S.R 124).length = band)
    (hrows : (S.R 116).length = rowCount)
    (hfresh : ∀ k ∈ [(94 : Fin 151),135,136,137,138], S.R k = []) :
    ∃ v', v'.user = v.user ∧ Exec body residentBandControls (mk v S)
      (residentBandControlsCost n band rowCount)
      (mk v' {S with R := (Function.update (Function.update (Function.update S.R 0 [])
        137 (List.replicate (n-(12*band+1)) tick))
        138 (List.replicate (min rowCount (n+(12*band+1)+1)-(n-(12*band+1))) tick))}) := by
  let W := 12*band+1
  obtain ⟨v₁,hu₁,he₁⟩ := residentBandWidth_exec (body := body) band v S hband
    (hfresh 94 (by simp)) (hfresh 135 (by simp))
  let S₁ : Stacks 151 A := {S with R := Function.update S.R 94 (List.replicate W tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := clippedBandControls_exec (body := body)
    (index := 0) (band := 94) (total := 116) (cursor := 137) (count := 138) (saved := 136) (tmp := 135)
    (by decide) n W rowCount v₁ S₁ (by simpa [S₁] using hn) (by simp [S₁])
    (by simpa [S₁] using hrows) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp))
  let S₂ : Stacks 151 A := {S₁ with R := (Function.update (Function.update S₁.R
    137 (List.replicate (n-W) tick)) 138 (List.replicate (min rowCount (n+W+1)-(n-W)) tick))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 94 v₂ S₂
  let S₃ : Stacks 151 A := {S₂ with R := Function.update S₂.R 94 []}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec body 0 v₃ S₃
  have hlen94 : (S₂.R 94).length = W := by simp [S₂,S₁]
  have hlen0 : (S₃.R 0).length = n := by simpa [S₃,S₂,S₁] using hn
  refine ⟨v₄,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast (by rw [hlen94,hlen0]; rfl) ?_⟩
  apply congrArg (mk v₄)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h0 : k = 0 <;> by_cases h94 : k = 94 <;> by_cases h137 : k = 137 <;> by_cases h138 : k = 138 <;>
    simp [S₃,S₂,S₁,W,h0,h94,h137,h138,hfresh 94 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
