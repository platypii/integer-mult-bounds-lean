module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBuildCouplingCoefficientPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientPageSize
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCountedLine

/-! Release exactly the owned coefficient-page prefix and its generated metadata. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def releaseCouplingCoefficientPage : Pr P₀ 144 Q A U :=
  .seq (retireCountedLine 139 94 138 109 104 105) (.seq (uclear 139) (uclear 140))

def releaseCouplingCoefficientPageCost (N L w : ℕ) : ℕ :=
  retireCountedLineCost N w+2*N+2+2*L+2

theorem releaseCouplingCoefficientPage_exec (w L : ℕ) (xs : List GaussianInt)
    (tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hcount : (S.R 139).length = xs.length) (hrows : (S.R 140).length = L) (hw : (S.R 94).length = w)
    (hpage : S.R 138 = cstream A w xs++tail)
    (h109 : S.R 109 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releaseCouplingCoefficientPageCost xs.length L w ∧
      Exec body releaseCouplingCoefficientPage (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 138 tail) 139 []) 140 [])}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := retireCountedLine_exec (body := body)
    139 94 138 109 104 105 (by decide) xs.length w (cstream A w xs) tail (by simp)
    v S hcount hw hpage h109 h104 h105
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 138 tail}
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body 139 v₁ S₁
  let S₂ : Stacks 144 A := {S₁ with R := Function.update S₁.R 139 []}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 140 v₂ S₂
  refine ⟨v₃,m₁+((2*(S₁.R 139).length+2)+(2*(S₂.R 140).length+2)),
    hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  have hc : (S₁.R 139).length = xs.length := by simpa [S₁] using hcount
  have hr : (S₂.R 140).length = L := by simpa [S₂,S₁] using hrows
  rw [hc,hr]
  dsimp only [releaseCouplingCoefficientPageCost]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
