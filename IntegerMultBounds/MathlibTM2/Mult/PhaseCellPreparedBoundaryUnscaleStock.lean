module

public import IntegerMultBounds.MathlibTM2.Host.EmbedStockTrace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryUnscale
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryScalingStock

/-! Prepared unscaling and publication reuse the generated scale reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.BandFactor
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

theorem preparedBoundaryUnscale_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (q p : ℕ) (hpq : p ≤ q/2) (xs : List GaussianInt)
    (hbound : ∀ z ∈ xs, |gv q z.re| ≤ 8*p+1 ∧ |gv q z.im| ≤ 8*p+1)
    (C : ℕ) (hpush : mnProgPush (cmulBlock (rsbCr boundaryFactorReg .dout .dtab .ya)
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) boundaryFactorMulReg
        boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .dout .dtab .ya))) ≤ C)
    (v : HS 226 Q A U) (S : Stacks 226 A)
    (hleft : ∀ i, (embStk preparedBoundaryCoreReg S).L i = [])
    (hmul : ∀ i : Fin 64, (embStk preparedBoundaryCoreReg S).R (boundaryFactorMulReg i) = [])
    (hready : RsbReady (boundaryFactorState (embStk preparedBoundaryCoreReg S)) (2*q+8) q)
    (hmaster : (S.R 119).length = q)
    (h184 : S.R 184 = []) (h220 : S.R 220 = []) (h221 : S.R 221 = [])
    (h223 : S.R 223 = []) (hya : S.R 208 = []) (hac2 : S.R 215 = [])
    (hsrc : S.R 217 = cstream A (2*q+8) xs) (h225 : S.R 225 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedBoundaryUnscaleCost q xs.length ∧
      ∀ depth, ExecWithin (embTab preparedBoundaryCoreReg body)
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (realScalarWorkspace C (2*q+8) xs.length+1000*(q+1))) depth
        (preparedBoundaryUnscale hQ) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 217 []) 224
          (cstream A (2*q+8) (xs.map (unscaleBoundaryWord q))++S.R 224))}) := by
  let T := embStk preparedBoundaryCoreReg S
  let ys := xs.map (unscaleBoundaryWord q)
  have hys : ys.length = xs.length := List.length_map ..
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generatedBoundaryUnscale_exec_within (body := body)
    hQ hA q p hpq xs hbound C hpush (embDn preparedBoundaryCoreReg v) T hleft hmul hready
    hmaster h184 h220 h221 h223 hya hac2 hsrc
  obtain ⟨v₁',hv₁',hu₁',he₁'⟩ := exec_emb_ovr (ι := id) (body' := embTab preparedBoundaryCoreReg body)
    preparedBoundaryCoreReg_injective (fun _ => rfl) (he₁ 0).toExec v rfl S rfl
  let S₁ : Stacks 226 A := {S with R := Function.update S.R 217 (cstream A (2*q+8) ys)}
  have he₁'' : Exec (embTab preparedBoundaryCoreReg body)
      (embProg preparedBoundaryCoreReg id (generatedBoundaryUnscale hQ))
      (mk v S) n₁ (mk v₁' S₁) := by
    convert he₁' using 1
    apply congrArg (mk v₁')
    symm
    change embOvr preparedBoundaryCoreReg
      ({T with R := Function.update T.R 217 (cstream A (2*q+8) ys)} : Stacks 224 A).get S = S₁
    rw [embOvr_updR preparedBoundaryCoreReg_injective,embOvr_stk]
    rfl
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec (embTab preparedBoundaryCoreReg body) 217 225 (by decide) id v₁' S₁
  let S₂ : Stacks 226 A := {S₁ with R := movedR S₁.R 217 225 id (S₁.R 217)}
  have h225' : S₂.R 225 = (cstream A (2*q+8) ys).reverse := by simp [S₂,S₁,movedR,h225]
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec (embTab preparedBoundaryCoreReg body) 225 224 (by decide) id v₂ S₂
  have hsize : (cstream A (2*q+8) ys).length = xs.length*(2*q+8) := by simp [hys]
  refine ⟨v₃,n₁+((2*(S₁.R 217).length+2)+(2*(S₂.R 225).length+2)),
    hu₃.trans (hu₂.trans (hu₁'.trans hu₁)),?_,?_⟩
  · simp only [S₁,Function.update_self,h225',List.length_reverse,hsize,preparedBoundaryUnscaleCost]
    nlinarith only [hn₁]
  · intro depth
    have ht₁ := exec_emb_within_stock_of_exec (ι := id) (body' := embTab preparedBoundaryCoreReg body) preparedBoundaryCoreReg_injective
      (fun _ => rfl) (he₁ depth) v rfl S rfl he₁''
    have ht₂ := moveR_within _ _ _ he₂ depth _ ht₁.final
    have ht₃ := moveR_within _ _ _ he₃ depth _ ht₂.final
    refine (ExecWithin.seq ht₁ (ExecWithin.seq ht₂ ht₃)).cast rfl ?_
    apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h217' : i = 217 <;> by_cases h224 : i = 224 <;>
      by_cases h225'' : i = 225 <;>
      simp [S₂,S₁,movedR,h217',h224,h225'',h225] <;> rfl


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
