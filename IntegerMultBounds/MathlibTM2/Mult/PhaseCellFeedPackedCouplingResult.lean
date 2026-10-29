module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpReverse
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Feed reversed local coupling rows to the next solve in natural order,
retaining the ambient-period header and both borrowed suffixes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

def feedPackedCouplingResult : Pr P₀ 168 Q A U :=
  .seq (toUnary 165 166 0 1 2)
    (.seq (reverseWords 166 104 94 113 110 105 106 108)
      (.seq (releaseFromDimensions 166 94 109 113 115 106 105) (uclear 166)))

theorem feedPackedCouplingResult_exec (V N w : ℕ) (hNV : N < 2^V)
    (xs : List GaussianInt) (hlen : xs.length = N) (tail : List (Fin (A+4)))
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = [])
    (hw : (S.R 94).length = w) (hsrc : S.R 113 = cstream A w xs.reverse++tail)
    (hfresh : ∀ r ∈ [(0 : Fin 168),1,2,104,105,106,108,109,115], S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 28*N*w+36*N+11*V+26 ∧
      Exec body feedPackedCouplingResult (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 113 tail) 110
          (cstream A w xs++S.R 110))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear (body := body)
    (a := 165) (z := 166) (w := 0) (t := 1) (t₂ := 2) (by decide) hNV v S h165
    (hfresh 0 (by simp)) (hfresh 1 (by simp)) (hfresh 2 (by simp))
  let B : Stacks 168 A := {S with R := Function.update S.R 166 (List.replicate N tick)}
  have he₁' : Exec body (toUnary 165 166 0 1 2) (mk v S) n₁ (mk v₁ B) := by
    simpa only [h166,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := reverseWords_coeffs_exec (body := body)
    (records := 166) (recordSaved := 104) (width := 94) (src := 113) (dst := 110)
    (saved := 105) (buf := 106) (tmp := 108) (by decide) w xs.reverse v₁ B tail
    (by simp [B,hlen]) (by simpa [B] using hsrc) (by simpa [B] using hw)
    (by simpa [B] using hfresh 104 (by simp)) (by simpa [B] using hfresh 105 (by simp))
    (by simpa [B] using hfresh 106 (by simp)) (by simpa [B] using hfresh 108 (by simp))
  let G : Stacks 168 A := {B with R := Function.update B.R 110 (cstream A w xs++B.R 110)}
  have he₂' : Exec body (reverseWords 166 104 94 113 110 105 106 108) (mk v₁ B)
      (N*(16*w+19)+6) (mk v₂ G) := by simpa [G,hlen] using he₂
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := releaseFromDimensions_exec (body := body)
    (a := 166) (b := 94) (count := 109) (src := 113) (saved := 115) (buf := 106) (tmp := 105)
    (by decide) v₂ G (cstream A w xs.reverse) tail
    (by simpa [G,B] using hsrc) (by simp [G,B,hlen,hw])
    (by simpa [G,B] using hfresh 109 (by simp)) (by simpa [G,B] using hfresh 115 (by simp))
    (by simpa [G,B] using hfresh 106 (by simp)) (by simpa [G,B] using hfresh 105 (by simp))
  let F : Stacks 168 A := {G with R := Function.update G.R 113 tail}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 166 v₃ F
  have hc : (F.R 166).length = N := by simp [F,G,B]
  have hm₃ : n₃ ≤ 12*(N*w)+9*N+12 := by simpa [G,B,hlen] using hn₃
  refine ⟨v₄,n₁+(N*(16*w+19)+6+(n₃+(2*N+2))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄))).cast (by rw [hc]) ?_⟩
  · nlinarith only [hn₁,hm₃]
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases h1 : r = 166 <;> by_cases h2 : r = 113 <;> by_cases h3 : r = 110 <;>
      simp [F,G,B,h1,h2,h3,h166]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
