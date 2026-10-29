module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellZeroPadLocalPrefix
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Decode the local length once, construct its padded ribbon and retain the
row count needed by the generated mask and later ribbon release. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def prepareLocalCouplingRibbon : Pr P 168 Q A U :=
  .seq (toUnary 165 127 0 1 2)
    (.seq (zeroPadLocalPrefix 127 100 94 132 160 108 158 104 105)
      (.seq (ucopy 127 166 109) (.seq (umul 2 100 166 109) (uclear 127))))

theorem prepareLocalCouplingRibbon_exec (V N band w : ℕ) (hNV : N < 2^V)
    (xs : List GaussianInt) (hx : xs.length = N) (tail : List (Fin (A+4)))
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hN : S.R 165 = binSyms V N) (hband : (S.R 100).length = band) (hw : (S.R 94).length = w)
    (hsource : S.R 132 = cstream A w xs++tail)
    (hclean : ∀ k ∈ [(0 : Fin 168),1,2,104,105,108,109,127,158,166], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 16*N*w+21*N+14*band*w+13*band+11*V+46 ∧
      Exec body prepareLocalCouplingRibbon (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 160
          (cstream A w (List.replicate band 0++xs++List.replicate band 0)++S.R 160))
          166 (List.replicate (N+2*band) tick))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := toUnary_exec_linear (body := body)
    (a := 165) (z := 127) (w := 0) (t := 1) (t₂ := 2) (by decide) hNV v S hN
    (hclean 0 (by simp)) (hclean 1 (by simp)) (hclean 2 (by simp))
  let B : Stacks 168 A := {S with R := Function.update S.R 127 (List.replicate N tick)}
  have he₁' : Exec body (toUnary 165 127 0 1 2) (mk v S) m₁ (mk v₁ B) := by
    simpa [B,hclean 127 (by simp)] using he₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := zeroPadLocalPrefix_exec (body := body)
    127 100 94 132 160 108 158 104 105 (by decide) N band w xs hx tail v₁ B
    (by simp [B]) (by simpa [B] using hband) (by simpa [B] using hw)
    (by simpa [B] using hsource) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · simpa [B] using hclean 108 (by simp)
      · simpa [B] using hclean 158 (by simp)
      · simpa [B] using hclean 104 (by simp)
      · simpa [B] using hclean 105 (by simp))
  let C : Stacks 168 A := {B with R := (Function.update B.R 160
    (cstream A w (List.replicate band 0++xs++List.replicate band 0)++B.R 160))}
  obtain ⟨v₃,hu₃,he₃⟩ := ucopy_exec (body := body) (a := 127) (b := 166) (t := 109)
    (by decide) (by decide) (by decide) v₂ C (by simpa [C,B] using hclean 109 (by simp))
  let D : Stacks 168 A := {C with R := Function.update C.R 166 (List.replicate N tick)}
  have he₃' : Exec body (ucopy 127 166 109) (mk v₂ C) (4*N+4) (mk v₃ D) := by
    simpa [D,C,B,hclean 166 (by simp)] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := umul_exec (body := body) 2 (a := 100) (b := 166) (t := 109)
    (by decide) (by decide) (by decide) v₃ D (by simpa [D,C,B] using hclean 109 (by simp))
  let F : Stacks 168 A := {D with R := Function.update D.R 166 (List.replicate (N+2*band) tick)}
  have he₄' : Exec body (umul 2 100 166 109) (mk v₃ D) (4*band+4) (mk v₄ F) := by
    simpa [F,D,C,B,hband,List.replicate_append_replicate,Nat.add_comm] using he₄
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec (body := body) 127 v₄ F
  have hlen : (F.R 127).length = N := by simp [F,D,C,B]
  refine ⟨v₅,m₁+(m₂+((4*N+4)+((4*band+4)+(2*N+2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),by nlinarith only [hm₁,hm₂],
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' (Exec.seq he₄' he₅)))).cast (by rw [hlen]) ?_⟩
  apply congrArg (mk v₅)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h127 : k = 127 <;> by_cases h166 : k = 166 <;> by_cases h160 : k = 160 <;>
    simp [F,D,C,B,h127,h166,h160,hclean 127 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
