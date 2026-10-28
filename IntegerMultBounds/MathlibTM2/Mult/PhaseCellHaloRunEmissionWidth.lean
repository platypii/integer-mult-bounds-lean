module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloRunController

/-! Select the physical emission width while preserving all scalar variables. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def haloRunEmissionWidth (flags : Bool) (W : ℕ) : ℕ := if flags then 1 else W

def setHaloRunEmissionWidth (flags : Bool) : Pr P 117 Q A U :=
  if flags then .seq (uclear 17) (.act (.push (.rt 17) (fun _ => tick) .done)) else .act .done

def setHaloRunEmissionWidthCost (flags : Bool) (W : ℕ) : ℕ := if flags then 2*W+3 else 1

theorem setHaloRunEmissionWidth_exec (flags : Bool) (W : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A) (h17 : S.R 17 = List.replicate W tick) :
    ∃ v', v'.user = v.user ∧
      Exec body (setHaloRunEmissionWidth flags) (mk v S) (setHaloRunEmissionWidthCost flags W)
        (mk v' {S with R := (Function.update S.R 17
          (List.replicate (haloRunEmissionWidth flags W) tick))}) := by
  cases flags with
  | false =>
    refine ⟨v,rfl,?_⟩
    have hr : Function.update S.R 17 (List.replicate W tick) = S.R := by
      rw [← h17,Function.update_eq_self]
    simpa [setHaloRunEmissionWidth,setHaloRunEmissionWidthCost,haloRunEmissionWidth,hr,Action.run]
      using Exec.act (body := body) (.done : Act 117 Q A U) (mk v S)
  | true =>
    obtain ⟨v₁,hu₁,he₁⟩ := uclear_exec (body := body) 17 v S
    let S₁ : Stacks 117 A := {S with R := Function.update S.R 17 []}
    have he₁' : Exec body (uclear 17) (mk v S) (2*W+2) (mk v₁ S₁) := by
      simpa [h17,S₁] using he₁
    have he₂ := Exec.act (body := body) (.push (.rt 17) (fun _ => tick) .done) (mk v₁ S₁)
    refine ⟨v₁,hu₁,(Exec.seq he₁' he₂).cast (by simp [setHaloRunEmissionWidthCost]) ?_⟩
    simp [haloRunEmissionWidth,Action.run,update_rt,S₁,Function.update_idem]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
