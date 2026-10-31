module

public import IntegerMultBounds.MathlibTM2.Host.BinArithStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyDescriptorInput
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Install the publication radius from its retained ordinary header. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem generatePublicationFrame_exec (work : Fin 263 → Fin T) (hwork : Function.Injective work)
    (radius width saved tmp carry : Fin T) (hreg : [radius,width,work 252,saved,tmp].Nodup)
    (r V : ℕ) (v : HS T Q A U) (S : Stacks T A) (M : Stacks 242 A)
    (hview : embStk work S = extendStacks (by decide : 242 ≤ 263) M)
    (hradius : (S.R radius).length = r) (hwidth : (S.R width).length = V)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ r*(4*V+10)+4*V+8 ∧
      embStk work {S with R := Function.update S.R (work 252) (binSyms V r)} = packedKeyPublicationInput M V r ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(4*V+4)) depth
        (toBinary radius width (work 252) saved tmp carry) (mk v S) n
        (mk v' {S with R := Function.update S.R (work 252) (binSyms V r)}) := by
  have hblank : S.R (work 252) = [] := by
    have hv := congrArg (fun C : Stacks 263 A => C.R 252) hview
    exact hv.trans (extendStacks_fresh (by decide : 242 ≤ 263) M 252 (by decide)).2
  obtain ⟨v',n,hu,hn,he⟩ := toBinary_exec_within (body := body) hreg carry v S hblank hsaved htmp depth
  rw [hradius,hwidth] at hn he
  refine ⟨v',n,hu,hn,?_,he⟩
  rw [embStk_updateR hwork,hview]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
