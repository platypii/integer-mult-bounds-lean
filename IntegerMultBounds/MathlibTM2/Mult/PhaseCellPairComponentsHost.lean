module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairComponentsData
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate the byte clock and assemble two retained real lines into a complex line. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def pairComponentLines : Pr P₀ 144 Q A U :=
  .seq (unaryProduct 121 94 131 134 135) (pairComponentsToFirst 131 132 137 140)

def pairComponentLinesCost (s w : ℕ) : ℕ := 10*s*w+9*s+8

theorem pairComponentLines_exec (hA : 4 ≤ A) (s w : ℕ) (xs ys : List GaussianInt)
    (hxlen : xs.length = s) (hylen : ys.length = s) (tailX tailY : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hs : (S.R 121).length = s) (hw : (S.R 94).length = w)
    (hx : S.R 132 = cstream A w xs++tailX) (hy : S.R 137 = cstream A w ys++tailY)
    (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) (h140 : S.R 140 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ pairComponentLinesCost s w ∧
      Exec body pairComponentLines (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 137 tailY)
          132 (cstream A w (List.zipWith pairComponentWord xs ys)++tailX))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 121) (b := 94) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v S h134 h135
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 131 (List.replicate (s*w) tick)}
  have he₁' : Exec body (unaryProduct 121 94 131 134 135) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hs,hw,h131] using he₁
  have hn₁' : n₁ ≤ s*(4*w+9)+4 := by simpa [hs,hw] using hn₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := pairComponentsToFirst_exec (body := body)
    (count := 131) (x := 132) (y := 137) (tmp := 140) (by decide) hA w xs ys
    (by omega) tailX tailY v₁ S₁ (by simp [S₁,hxlen])
    (by simpa [S₁] using hx) (by simpa [S₁] using hy) (by simpa [S₁] using h140)
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁' he₂).cast rfl ?_⟩
  · dsimp [pairComponentLinesCost]
    rw [hxlen] at hn₂
    nlinarith only [hn₁',hn₂]
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h1 : k = 131 <;> by_cases h2 : k = 132 <;> by_cases h3 : k = 137 <;>
      simp [S₁,h1,h2,h3,h131]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
