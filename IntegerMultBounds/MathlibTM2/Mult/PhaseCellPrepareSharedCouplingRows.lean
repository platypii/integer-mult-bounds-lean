module

public import IntegerMultBounds.MathlibTM2.Node.Params

/-! Restore the retained page's row-width frame after cell publication releases
its control port. The shared band master is preserved. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def prepareSharedCouplingRows : Pr P 168 Q A U :=
  .seq (umul 2 124 140 135) (.act (.push (.rt 140) (fun _ => tick) .done))

theorem prepareSharedCouplingRows_exec (band : ℕ) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hband : (S.R 124).length = band) (h140 : S.R 140 = []) (h135 : S.R 135 = []) :
    ∃ v', v'.user = v.user ∧ Exec body prepareSharedCouplingRows (mk v S) (4*band+5)
      (mk v' {S with R := Function.update S.R 140 (List.replicate (2*band+1) tick)}) := by
  obtain ⟨v',hu,he⟩ := umul_exec (body := body) 2 (a := 124) (b := 140) (t := 135)
    (by decide) (by decide) (by decide) v S h135
  let B : Stacks 168 A := {S with R := Function.update S.R 140 (List.replicate (2*band) tick)}
  have he' : Exec body (umul 2 124 140 135) (mk v S) (4*band+4) (mk v' B) := by
    simpa [B,hband,h140] using he
  have hp := Exec.act (body := body) (.push (.rt 140) (fun _ => tick) .done) (mk v' B)
  refine ⟨v',hu,(Exec.seq he' hp).cast (by omega) ?_⟩
  simp [Action.run,update_rt,B,List.replicate_succ]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
