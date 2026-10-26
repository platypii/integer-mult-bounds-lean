module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Transfer generated keys/count into the protected caller, retain its width
headers and release the private generated operands. Two moves preserve packet
order while one move suffices for the unary count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 144 Q A U}

def installKeyRuntime : Pr P₀ 144 Q A U :=
  .seq (ucopy 115 125 133) (.seq (ucopy 94 130 133)
    (.seq (moveR 87 138 id) (.seq (moveR 138 126 id)
      (.seq (moveR 86 127 id) (clearWords [94,115])))))

def installedKeyRuntimeR (R : Regs 144 A) (V w K : ℕ) (keys : List (Fin (A+4))) : Regs 144 A :=
  Function.update (Function.update (Function.update (Function.update
    (fun k => if k ∈ [(86 : Fin 144),87,94,115] then [] else R k)
    125 (List.replicate V tick)) 126 (keys++R 126)) 127 (List.replicate K tick)) 130 (List.replicate w tick)

theorem installKeyRuntime_exec (V w K : ℕ) (keys : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (h115 : (S.R 115).length = V) (h94 : (S.R 94).length = w)
    (h87 : S.R 87 = keys) (h86 : S.R 86 = List.replicate K tick)
    (hfresh : ∀ k ∈ [(125 : Fin 144),127,130,133,138], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body installKeyRuntime (mk v S) (6*(V+w)+4*keys.length+2*K+19)
        (mk v' { S with R := installedKeyRuntimeR S.R V w K keys }) := by
  have h125 := hfresh 125 (by simp)
  have h127 := hfresh 127 (by simp)
  have h130 := hfresh 130 (by simp)
  have h133 := hfresh 133 (by simp)
  have h138 := hfresh 138 (by simp)
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := 115) (b := 125) (t := 133)
    (by decide) (by decide) (by decide) v S h133
  let S₁ : Stacks 144 A := { S with R := Function.update S.R 125 (List.replicate V tick) }
  have he₁' : Exec body (ucopy 115 125 133) (mk v S) (4*V+4) (mk v₁ S₁) := by simpa [S₁,h115,h125] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) (a := 94) (b := 130) (t := 133)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using h133)
  let S₂ : Stacks 144 A := { S₁ with R := Function.update S₁.R 130 (List.replicate w tick) }
  have he₂' : Exec body (ucopy 94 130 133) (mk v₁ S₁) (4*w+4) (mk v₂ S₂) := by simpa [S₂,S₁,h94,h130] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body 87 138 (by decide) id v₂ S₂
  let S₃ : Stacks 144 A := { S₂ with R := movedR S₂.R 87 138 id (S₂.R 87) }
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec body 138 126 (by decide) id v₃ S₃
  let S₄ : Stacks 144 A := { S₃ with R := movedR S₃.R 138 126 id (S₃.R 138) }
  obtain ⟨v₅,hu₅,he₅⟩ := moveR_exec body 86 127 (by decide) id v₄ S₄
  let S₅ : Stacks 144 A := { S₄ with R := movedR S₄.R 86 127 id (S₄.R 86) }
  obtain ⟨v₆,hu₆,he₆⟩ := clearWords_exec (body := body) [(94 : Fin 144),115] (by decide) v₅ S₅
  refine ⟨v₆,hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))))).cast ?_ ?_⟩
  · simp [S₅,S₄,S₃,S₂,S₁,movedR,h87,h86,h138,h94,h115]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h861 : k = 86
    · subst k
      simp [S₅,S₄,S₃,S₂,S₁,movedR,installedKeyRuntimeR,h87,h86,h138,h127]
    by_cases h871 : k = 87
    · subst k
      simp [S₅,S₄,S₃,S₂,S₁,movedR,installedKeyRuntimeR,h87,h86,h138,h127]
    by_cases h941 : k = 94
    · subst k
      simp [installedKeyRuntimeR]
    by_cases h1151 : k = 115
    · subst k
      simp [installedKeyRuntimeR]
    by_cases h1251 : k = 125
    · subst k
      simp [S₅,S₄,S₃,S₂,S₁,movedR,installedKeyRuntimeR,h87,h86,h138,h127]
    by_cases h1261 : k = 126
    · subst k
      simp [S₅,S₄,S₃,S₂,S₁,movedR,installedKeyRuntimeR,h87,h86,h138,h127]
    by_cases h1271 : k = 127
    · subst k
      simp [S₅,S₄,S₃,S₂,S₁,movedR,installedKeyRuntimeR,h87,h86,h138,h127]
    by_cases h1301 : k = 130
    · subst k
      simp [S₅,S₄,S₃,S₂,S₁,movedR,installedKeyRuntimeR,h87,h86,h138,h127]
    by_cases h1381 : k = 138
    · subst k
      simp [S₅,S₄,S₃,S₂,S₁,movedR,installedKeyRuntimeR,h87,h86,h138,h127]
    simp [S₅,S₄,S₃,S₂,S₁,movedR,installedKeyRuntimeR,
      h861,h871,h941,h1151,h1251,h1261,h1271,h1301,h1381]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
