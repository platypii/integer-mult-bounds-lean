module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginPacketWidths
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenOriginPackets

/-! Construct the numerical packet-width counter while keeping the geometry counter. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def prepareOriginWidening : Pr P₀ 117 Q A U :=
  .seq (moveR 115 24 id) (.seq generateWeightWidth
    (.seq (moveR 115 19 id) (moveR 24 115 id)))

theorem prepareOriginWidening_exec (P q w t u V : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hw : (S.R 94).length = w) (ht : (S.R 98).length = t) (hu : (S.R 99).length = u)
    (hV : (S.R 115).length = V)
    (hfresh : ∀ k ∈ [(0 : Fin 117),1,2,3,4,19,24,104], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ weightWidthCost P q w t u+4*V+2*weightWorkspaceWidth P q w t u+6 ∧
      Exec body prepareOriginWidening (mk v S) n
        (mk v' {S with R := (Function.update S.R 19
          (List.replicate (weightWorkspaceWidth P q w t u) tick))}) := by
  let W := weightWorkspaceWidth P q w t u
  obtain ⟨v₁,hu₁,he₁⟩ := moveR_exec (body := body) 115 24 (by decide) id v S
  let S₁ : Stacks 117 A := {S with R := movedR S.R 115 24 id (S.R 115)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := generateWeightWidth_exec (body := body) P q w t u v₁ S₁
    (by simpa [S₁,movedR] using hP) (by simpa [S₁,movedR] using hq)
    (by simpa [S₁,movedR] using hw) (by simpa [S₁,movedR] using ht)
    (by simpa [S₁,movedR] using hu) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [S₁,movedR,hfresh])
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 115 (List.replicate W tick)}
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec (body := body) 115 19 (by decide) id v₂ S₂
  let S₃ : Stacks 117 A := {S₂ with R := movedR S₂.R 115 19 id (S₂.R 115)}
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec (body := body) 24 115 (by decide) id v₃ S₃
  refine ⟨v₄,(2*(S.R 115).length+2)+(n₂+((2*(S₂.R 115).length+2)+(2*(S₃.R 24).length+2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast rfl ?_⟩
  · simp [S₃,S₂,S₁,movedR,hfresh 24 (by simp),hV]
    dsimp only [W] at *
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk19 : k = 19
    · subst k; simp [S₃,S₂,S₁,movedR,hfresh 19 (by simp),W]
    by_cases hk24 : k = 24
    · subst k; simp [S₃,S₂,S₁,movedR,hfresh 24 (by simp)]
    by_cases hk115 : k = 115
    · subst k; simp [S₃,S₂,S₁,movedR,hfresh 24 (by simp)]
    simp [S₃,S₂,S₁,movedR,hk19,hk24,hk115]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
