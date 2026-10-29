module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCouplingAdvance
public import IntegerMultBounds.MathlibTM2.Fast.Input

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node

/-- Restore the binary zero offset after a positive or negative pass. -/
def packedCouplingReset {P U : Type} {Q A : ℕ} : Pr P 117 Q A U :=
  .seq (uclear 105) (copyR 106 105 0 id)

theorem packedCouplingReset_exec {P U : Type} {Q A V d : ℕ}
    {body : P → Pr P 117 Q A U} (v : HS 117 Q A U) (S : Stacks 117 A)
    (hd : S.R 105 = binSyms V d) (hz : S.R 106 = binSyms V 0) (htmp : S.R 0 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body packedCouplingReset (mk v S) (6*V+6)
        (mk v' {S with R := Function.update S.R 105 (binSyms V 0)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := uclear_exec (body := body) 105 v S
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 105 []}
  obtain ⟨v₂,hu₂,he₂⟩ := copyR_exec (body := body) 106 105 0
    (by decide) (by decide) (by decide) id v₁ S₁ (by simpa [S₁] using htmp)
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ ?_⟩
  · simp [S₁,hd,hz]
    omega
  · apply congrArg (mk v₂)
    simp [S₁,hz,binSyms]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
