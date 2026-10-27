module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBuildCouplingPageCache
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCouplingCoefficientPage

/-! Release the retained guard stream, coefficient page and their owned metadata. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def releaseCouplingPageCache : Pr P₀ 144 Q A U := .seq (uclear 135) releaseCouplingCoefficientPage

def releaseCouplingPageCacheCost (s N L w : ℕ) : ℕ := 2*s+2+releaseCouplingCoefficientPageCost N L w

theorem releaseCouplingPageCache_exec (s w L : ℕ) (xs : List GaussianInt)
    (tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hguard : (S.R 135).length = s) (hcount : (S.R 139).length = xs.length)
    (hrows : (S.R 140).length = L) (hw : (S.R 94).length = w)
    (hpage : S.R 138 = cstream A w xs++tail)
    (h109 : S.R 109 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releaseCouplingPageCacheCost s xs.length L w ∧
      Exec body releaseCouplingPageCache (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R 135 [])
          138 tail) 139 []) 140 [])}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := uclear_exec body 135 v S
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 135 []}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := releaseCouplingCoefficientPage_exec (body := body)
    w L xs tail v₁ S₁ (by simpa [S₁] using hcount) (by simpa [S₁] using hrows)
    (by simpa [S₁] using hw) (by simpa [S₁] using hpage) (by simpa [S₁] using h109)
    (by simpa [S₁] using h104) (by simpa [S₁] using h105)
  refine ⟨v₂,(2*s+2)+m₂,hu₂.trans hu₁,Nat.add_le_add_left hm₂ _,(Exec.seq he₁ he₂).cast ?_ rfl⟩
  rw [hguard]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
