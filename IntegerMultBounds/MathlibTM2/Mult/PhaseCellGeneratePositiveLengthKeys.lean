module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparePositiveLengthKeys

/-! Generate the positive distinct length-key queue from ordinary parameters.
Candidate discovery and selection share width sources; all workspace is released. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generatePositiveLengthKeys : Pr P₀ 117 Q A U := .seq preparePositiveLengthKeys (clearWords [94,115])

def generatePositiveLengthKeysCost (P q s t u band : ℕ) : ℕ :=
  let V := weightWorkspaceWidth P q (2*q+8) t u
  generateLengthCandidatesCost P q s t u band+(21*tblC V V+230*V+263)

theorem generatePositiveLengthKeys_exec (P q s t u band : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115, 86], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generatePositiveLengthKeysCost P q s t u band ∧
      Exec body generatePositiveLengthKeys (mk v S) n
        (mk v' { S with R := (Function.update (Function.update S.R 87
          (naturalPositiveLengthPackets A (weightWorkspaceWidth P q (2*q+8) t u) s t band ++ S.R 87))
          86 (List.replicate (naturalPositiveLengthKeys s t band).length tick)) }) := by
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := preparePositiveLengthKeys_exec (body := body)
    P q s t u band hP hs hst hu hband hA v S hPSrc hq hsSrc htSrc huSrc hbSrc hblank hfresh
  let S₁ : Stacks 117 A := { S with R := preparedPositiveLengthR A P q s t u band S.R }
  obtain ⟨v₂,hu₂,he₂⟩ := clearWords_exec (body := body) [(94 : Fin 117),115] (by decide) v₁ S₁
  have hsum : (([(94 : Fin 117),115]).map (fun k => (S₁.R k).length)).sum = w+V := by
    simp [S₁,preparedPositiveLengthR,w,V]
  refine ⟨v₂,n₁+(2*(w+V)+5),hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp only [preparePositiveLengthKeysCost,generatePositiveLengthKeysCost,generateLengthCandidatesCost] at *
    dsimp only [w,V] at *
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h94 : k = 94
    · subst k; simp [hfresh 94 (by simp)]
    by_cases h115 : k = 115
    · subst k; simp [hfresh 115 (by simp)]
    simp [S₁,preparedPositiveLengthR,Function.update_apply,h94,h115]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
