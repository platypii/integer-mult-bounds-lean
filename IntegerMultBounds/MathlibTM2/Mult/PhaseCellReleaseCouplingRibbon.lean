module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareRibbonLength
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease

/-! Release the local source after its restored coupling pass. Both the word
count and the symbol count are generated from retained headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def releaseCouplingRibbon : Pr P 168 Q A U :=
  .seq prepareRibbonLength
    (.seq (releaseFromDimensions 166 94 108 141 167 104 105) (uclear 166))

theorem releaseCouplingRibbon_exec (V N band w : ℕ) (hNV : N < 2^V)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (xs tail : List (Fin (A+4))) (hsrc : S.R 141 = xs++tail)
    (hlen : xs.length = (N+2*band)*w)
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = [])
    (hband : (S.R 100).length = band) (hw : (S.R 94).length = w)
    (h109 : S.R 109 = []) (h0 : S.R 0 = []) (h1 : S.R 1 = []) (h2 : S.R 2 = [])
    (h108 : S.R 108 = []) (h167 : S.R 167 = [])
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 12*((N+2*band)*w)+17*N+26*band+11*V+24 ∧
      Exec body releaseCouplingRibbon (mk v S) n
        (mk v' {S with R := Function.update S.R 141 tail}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareRibbonLength_exec (body := body) V N band hNV v S
    h165 h166 hband h109 h0 h1 h2
  let B : Stacks 168 A := {S with R := Function.update S.R 166 (List.replicate (N+2*band) tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := releaseFromDimensions_exec (body := body)
    (a := 166) (b := 94) (count := 108) (src := 141) (saved := 167) (buf := 104) (tmp := 105)
    (by decide) v₁ B xs tail (by simpa [B] using hsrc)
    (by simpa [B,hw] using hlen)
    (by simpa [B] using h108) (by simpa [B] using h167)
    (by simpa [B] using h104) (by simpa [B] using h105)
  let F : Stacks 168 A := {B with R := Function.update B.R 141 tail}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 166 v₂ F
  have hc : (F.R 166).length = N+2*band := by simp [F,B]
  have hb : (B.R 166).length = N+2*band := by simp [B]
  refine ⟨v₃,n₁+(n₂+(2*(N+2*band)+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hc]) ?_⟩
  · rw [hb,hlen] at hn₂
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases h : r = 166 <;> by_cases hsrc : r = 141 <;> simp [F,B,h,hsrc,h166]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
