module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareHaloLengthKeys

/-! Generate the positive distinct length-key queue from ordinary halo parameters.
Candidate discovery and selection share width sources; all workspace is released. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateHaloLengthKeys : Pr P₀ 117 Q A U := .seq prepareHaloLengthKeys (clearWords [94,115])

def generateHaloLengthKeysCost (P q s t u band a b : ℕ) : ℕ :=
  let V := weightWorkspaceWidth P q (2*q+8) t u
  prepareHaloLengthKeysCost P q s t u band a b+2*((2*q+8)+V)+5

theorem generateHaloLengthKeys_exec (P q s t u band a b : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115, 86], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generateHaloLengthKeysCost P q s t u band a b ∧
      Exec body generateHaloLengthKeys (mk v S) n
        (mk v' { S with R := (Function.update (Function.update S.R 87
          (haloPositiveLengthPackets A (weightWorkspaceWidth P q (2*q+8) t u) s t band a b ++ S.R 87))
          86 (List.replicate (haloLengthKeys s t band a b).length tick)) }) := by
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareHaloLengthKeys_exec (body := body)
    P q s t u band a b hP hs hst hu hband has hbs hA v S hPSrc hq hsSrc htSrc huSrc hbSrc haSrc hbEndSrc hblank hfresh
  let S₁ : Stacks 117 A := { S with R := preparedHaloLengthR A P q s t u band a b S.R }
  obtain ⟨v₂,hu₂,he₂⟩ := clearWords_exec (body := body) [(94 : Fin 117),115] (by decide) v₁ S₁
  have hsum : (([(94 : Fin 117),115]).map (fun k => (S₁.R k).length)).sum = w+V := by
    simp [S₁,preparedHaloLengthR,w,V]
  refine ⟨v₂,n₁+(2*(w+V)+5),hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp only [generateHaloLengthKeysCost] at *
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
    simp [S₁,preparedHaloLengthR,Function.update_apply,h94,h115]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
