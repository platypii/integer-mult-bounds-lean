module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClippedBandControls

/-! Add the current clipped block size to an address accumulator and advance its cursor. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def packedSizeStep : Pr P 154 Q A U :=
  .seq (clippedBandControls 151 94 116 137 138 136 135)
    (.seq (ucopy 138 0 135) (.seq (clearWords [137,138])
      (.act (.push (.rt 151) (fun _ => tick) .done))))

def packedSizeStepCost (n W N : ℕ) : ℕ :=
  let L := min N (n+W+1)-(n-W)
  clippedBandControlsCost n W N+((4*L+4)+((2*((n-W)+L)+5)+1))

theorem packedSizeStep_exec (n W N : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hn : (S.R 151).length = n) (hW : (S.R 94).length = W) (hN : (S.R 116).length = N)
    (hfresh : ∀ k ∈ [(135 : Fin 154),136,137,138], S.R k = []) :
    ∃ v', v'.user = v.user ∧ Exec body packedSizeStep (mk v S) (packedSizeStepCost n W N)
      (mk v' {S with R := (Function.update (Function.update S.R 0
        (List.replicate (min N (n+W+1)-(n-W)) tick++S.R 0)) 151 (tick::S.R 151))}) := by
  let L := min N (n+W+1)-(n-W)
  obtain ⟨v₁,hu₁,he₁⟩ := clippedBandControls_exec (body := body)
    (index := 151) (band := 94) (total := 116) (cursor := 137) (count := 138) (saved := 136) (tmp := 135)
    (by decide) n W N v S hn hW hN (by
      intro k hk
      exact hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto))
  let S₁ : Stacks 154 A := {S with R := (Function.update (Function.update S.R 137
    (List.replicate (n-W) tick)) 138 (List.replicate L tick))}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec body (a := 138) (b := 0) (t := 135)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 135 (by simp))
  let S₂ : Stacks 154 A := {S₁ with R := Function.update S₁.R 0 (List.replicate L tick++S.R 0)}
  have he₂' : Exec body (ucopy 138 0 135) (mk v₁ S₁) (4*L+4) (mk v₂ S₂) := by
    simpa [S₂,S₁] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [(137 : Fin 154),138] (by decide) v₂ S₂
  let S₃ : Stacks 154 A := {S with R := Function.update S.R 0 (List.replicate L tick++S.R 0)}
  have he₃' : Exec body (clearWords [137,138]) (mk v₂ S₂) (2*((n-W)+L)+5) (mk v₃ S₃) := by
    convert he₃ using 1
    · simp [S₂,S₁]
    · apply congrArg (mk v₃)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hk0 : k = 0 <;> by_cases hk137 : k = 137 <;> by_cases hk138 : k = 138 <;>
        simp [S₃,S₂,S₁,hk0,hk137,hk138,hfresh 137 (by simp),hfresh 138 (by simp)]
  have he₄ := Exec.act (body := body) (.push (.rt 151) (fun _ => tick) .done) (mk v₃ S₃)
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' he₄))).cast rfl ?_⟩
  simp [S₃,Action.run,update_rt,L]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
