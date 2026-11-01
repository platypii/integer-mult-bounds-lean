module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishReplicaCouplingRow

/-! Retire the overwritten residual/RHS prefixes and archive the recovered row.
Reuse the existing discard-and-archive transition; borrowed suffixes restore. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 255 Q A U}

def retireReplicaRecoveryRow : Pr P 255 Q A U :=
  .seq (discardPrefix 251 110 104 105) (finishReplicaCouplingRow 251 110 132 125 104 105)

def retiredReplicaRecoveryState (S : Stacks 255 A) (rhsTail outputTail words : List (Fin (A+4))) : Stacks 255 A :=
  {S with R := (Function.update (Function.update (Function.update S.R 110 rhsTail) 132 outputTail)
    125 (words++S.R 125))}

theorem retireReplicaRecoveryRow_exec (V : ℕ) (xs rhs words rhsTail outputTail : List (Fin (A+4)))
    (hxs : xs.length = V) (hrhs : rhs.length = V) (hwords : words.length = V)
    (v : HS 255 Q A U) (S : Stacks 255 A) (hV : (S.R 251).length = V)
    (h110 : S.R 110 = xs++(rhs++rhsTail)) (h132 : S.R 132 = words++outputTail)
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body retireReplicaRecoveryRow (mk v S) (18*V+18)
        (mk v' (retiredReplicaRecoveryState S rhsTail outputTail words)) := by
  obtain ⟨v₁,hu₁,he₁⟩ := discardPrefix_exec (body := body) (count := 251) (src := 110)
    (trash := 104) (tmp := 105) (by decide) xs (rhs++rhsTail) v S h110 (by rw [hV,hxs]) h104 h105
  let J : Stacks 255 A := {S with R := Function.update S.R 110 (rhs++rhsTail)}
  obtain ⟨v₂,hu₂,he₂⟩ := finishReplicaCouplingRow_exec_within (body := body) 251 110 132 125 104 105
    (by decide) V rhs words rhsTail outputTail hrhs hwords v₁ J
    (by simpa [J] using hV) (by simp [J]) (by simpa [J] using h132)
    (by simpa [J] using h104) (by simpa [J] using h105) 0
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂.toExec).cast ?_ ?_⟩
  · unfold finishReplicaCouplingRowCost
    rw [hxs]
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp [J,retiredReplicaRecoveryState,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
