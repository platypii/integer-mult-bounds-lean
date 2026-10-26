module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareOriginControls

/-! Generate origins/count and release the retained width headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateOriginControls : Pr P₀ 117 Q A U :=
  .seq prepareOriginControls (clearWords [94,115])

def generateOriginControlsCost (P q s t u band L : ℕ) : ℕ :=
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  4*q+5 + weightWidthCost P q w t u +
    unaryOriginControllerCost P q w s t u band L + (62*V+63) + 2*(w+V)+5

theorem generateOriginControls_exec (P q s t u band L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hLSrc : (S.R 102).length = L)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115, 116], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generateOriginControlsCost P q s t u band L ∧
      Exec body generateOriginControls (mk v S) m
        (mk v' { S with R := originControlsR A (weightWorkspaceWidth P q (2*q+8) t u) s t band L S.R }) := by
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := prepareOriginControls_exec (body := body)
    P q s t u band L hP hs hst hu hband hL hLs hA v S hPSrc hq hsSrc htSrc huSrc hbSrc hLSrc hblank hfresh
  let S₁ : Stacks 117 A := { S with R := preparedOriginR A P q s t u band L S.R }
  obtain ⟨v₂,hu₂,he₂⟩ := clearWords_exec (body := body) [(94 : Fin 117),115] (by decide) v₁ S₁
  have hsum : (([(94 : Fin 117),115]).map (fun k => (S₁.R k).length)).sum = w+V := by
    simp [S₁,preparedOriginR,originControlsR,w,V]
  refine ⟨v₂,m₁+(2*(w+V)+5),hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp only [generateOriginControlsCost,prepareOriginControlsCost] at *
    dsimp only [w,V] at *
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h94 : k = 94
    · subst k; simp [originControlsR,hfresh 94 (by simp)]
    by_cases h115 : k = 115
    · subst k; simp [originControlsR,hfresh 115 (by simp)]
    simp [S₁,preparedOriginR,originControlsR,Function.update_apply,h94,h115]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
