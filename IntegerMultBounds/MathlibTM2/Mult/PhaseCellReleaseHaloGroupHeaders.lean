module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloOuterHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseGroupHeaders

/-! Release private endpoint and ordinary header copies,
leaving retained endpoints, parameters and ambient payloads untouched. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 144 Q A U}

def releaseHaloGroupHeaders : Pr P 144 Q A U :=
  .seq (clearWords [111,113]) releaseGroupHeaders

theorem releaseHaloGroupHeaders_exec (P N q l s t u band a b L : ℕ)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hfresh : ∀ r ∈ groupHeaderCopies, S.R r.2 = [])
    (h111 : S.R 111 = []) (h113 : S.R 113 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body releaseHaloGroupHeaders (mk v { S with R := copiedHaloGroupR P N q l s t u band a b L S.R })
        (2*(P+N+q+l+s+t+u+band+2*L+a+b)+26) (mk v' S) := by
  let S₁ : Stacks 144 A := { S with R := copiedHaloGroupR P N q l s t u band a b L S.R }
  obtain ⟨v₁,hu₁,he₁⟩ := clearWords_exec (body := body) [(111 : Fin 144),113] (by decide) v S₁
  have hsum : (([(111 : Fin 144),113]).map (fun k => (S₁.R k).length)).sum = a+b := by
    simp [S₁,copiedHaloGroupR]
  have he₁' : Exec body (clearWords [111,113]) (mk v S₁) (2*(a+b)+5)
      (mk v₁ { S with R := copiedGroupR P N q l s t u band L S.R }) := by
    refine he₁.cast (by rw [hsum]; rfl) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h111' : k = 111
    · subst k; simp [copiedGroupR_endpoint P N q l s t u band L S.R 111 (by simp),h111]
    by_cases h113' : k = 113
    · subst k; simp [copiedGroupR_endpoint P N q l s t u band L S.R 113 (by simp),h113]
    simp [S₁,copiedHaloGroupR,h111',h113']
  obtain ⟨v₂,hu₂,he₂⟩ := releaseGroupHeaders_exec (body144 := body) P N q l s t u band L v₁ S hfresh
  exact ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' he₂).cast (by ring) rfl⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
