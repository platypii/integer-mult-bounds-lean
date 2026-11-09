module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentWorkspace
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Lift a two-port component execution without recounting its spectator bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

theorem componentExec_twoPorts_within (p : Pr P₀ 144 Q A U) (v : HS 148 Q A U) (S : Stacks 148 A)
    (v' : HS 144 Q A U) (n work : ℕ) (input output : List (Fin (A+4)))
    (hu : v'.user = v.user)
    (he : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk (embDn componentReg v) (embStk componentReg S))+0+work)
      0 p (mk (embDn componentReg v) (embStk componentReg S)) n
      (mk v' {(embStk componentReg S) with R := (Function.update
        (Function.update (embStk componentReg S).R 110 input) 132 output)})) :
    ∃ v'', v''.user = v.user ∧ ExecWithin (embTab componentReg body)
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+work)
      0 (embProg componentReg id p)
      (mk v S) n (mk v'' {S with R := Function.update (Function.update S.R 110 input) 132 output}) := by
  have hbody : ∀ p, (embTab componentReg body) (id p) = embProg componentReg id (body p) := fun _ => rfl
  obtain ⟨v'',hv'',hu'',he''⟩ := exec_emb_ovr_within_stock componentReg (ι := id) (body' := embTab componentReg body)
    componentReg_injective hbody he v rfl S rfl
  refine ⟨v'',hu''.trans hu,he''.cast rfl ?_⟩
  apply congrArg (mk v'')
  let B := embStk componentReg S
  let B₁ : Stacks 144 A := {B with R := Function.update B.R 110 input}
  rw [embOvr_updR componentReg_injective B₁ S 132 output,
    embOvr_updR componentReg_injective B S 110 input,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
