module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplayWeightPage

/-! Move an actually generated weight page into retained storage and build its replay clock. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 121 Q A U}

def cacheWeightPage : Pr P 121 Q A U :=
  .seq (ucopy 64 118 119)
    (.seq (ucopy 64 118 119) (takePrefix 118 110 117 119 120))

theorem cacheWeightPage_exec (v : HS 121 Q A U) (S : Stacks 121 A)
    (page tail : List (Fin (A+4))) (n : ℕ) (hlen : page.length = 2*n)
    (hsource : S.R 110 = page++tail) (hrow : (S.R 64).length = n)
    (h118 : S.R 118 = []) (h119 : S.R 119 = []) (h120 : S.R 120 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body cacheWeightPage (mk v S) (20*n+14)
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 110 tail)
          117 (page++S.R 117)) 118 (List.replicate (2*n) tick))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (t := 119)
    (show (64 : Fin 121) ≠ 118 by decide) (by decide) (by decide) v S h119
  let S₁ : Stacks 121 A := {S with R := (Function.update S.R 118
    (List.replicate (S.R 64).length tick++S.R 118))}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) (t := 119)
    (show (64 : Fin 121) ≠ 118 by decide) (by decide) (by decide) v₁ S₁ (by simp [S₁,h119])
  let S₂ : Stacks 121 A := {S₁ with R := (Function.update S₁.R 118
    (List.replicate (S₁.R 64).length tick++S₁.R 118))}
  have hclock : S₂.R 118 = List.replicate (2*n) tick := by
    simp [S₂,S₁,hrow,h118,← List.replicate_add,two_mul]
  obtain ⟨v₃,hu₃,he₃⟩ := takePrefix_exec (body := body)
    (show [(118 : Fin 121),110,117,119,120].Nodup by decide)
    v₂ S₂ page tail (by simpa [S₂,S₁] using hsource)
    (by rw [hclock,List.length_replicate,hlen]) (by simp [S₂,S₁,h119]) (by simp [S₂,S₁,h120])
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp only [S₁,Function.update_of_ne (show (64 : Fin 121) ≠ 118 by decide),hrow,hlen]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h110 : i = 110 <;> by_cases h117 : i = 117 <;> by_cases hi118 : i = 118 <;>
      simp [S₂,S₁,hrow,h118,← List.replicate_add,two_mul,h110,h117,hi118]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
