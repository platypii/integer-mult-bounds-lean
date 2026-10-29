module

public import IntegerMultBounds.MathlibTM2.Host.BinArith
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Construct the sweep's unary width and row count from retained headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 168 Q A U}

def prepareCoreGatherHeaders : Pr P 168 Q A U :=
  .seq (ucopy 163 115 104) (toUnary 165 103 104 105 106)

theorem prepareCoreGatherHeaders_exec (V L : ℕ) (hL : L < 2^V)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (h163 : (S.R 163).length = V) (h165 : S.R 165 = binSyms V L)
    (hfresh : ∀ k ∈ [(103 : Fin 168), 104, 105, 106, 115], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 6*L+15*V+10 ∧
      Exec body prepareCoreGatherHeaders (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 115
          (List.replicate V tick)) 103 (List.replicate L tick))}) := by
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := 163) (b := 115) (t := 104)
    (by decide) (by decide) (by decide) v S (hfresh 104 (by simp))
  let S₁ : Stacks 168 A := {S with R := Function.update S.R 115 (List.replicate V tick)}
  have he₁' : Exec body (ucopy 163 115 104) (mk v S) (4*V+4) (mk v₁ S₁) := by
    simpa [S₁, h163, hfresh 115 (by simp)] using he₁
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := toUnary_exec_linear body
    (a := 165) (z := 103) (w := 104) (t := 105) (t₂ := 106) (by decide) hL v₁ S₁
    (by simpa [S₁] using h165)
    (by simpa [S₁] using hfresh 104 (by simp))
    (by simpa [S₁] using hfresh 105 (by simp))
    (by simpa [S₁] using hfresh 106 (by simp))
  refine ⟨v₂, (4*V+4)+n₂, hu₂.trans hu₁, by omega, ?_⟩
  simpa [prepareCoreGatherHeaders, S₁, hfresh 103 (by simp)] using Exec.seq he₁' he₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
