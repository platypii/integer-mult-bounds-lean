module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundarySolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryUnscale

/-! Undo boundary normalization and publish over a borrowed suffix without disturbing the factor page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

noncomputable def preparedBoundaryUnscale (hQ : SS.states ≤ Q) : Pr P 226 Q A U :=
  .seq (embProg preparedBoundaryCoreReg id (generatedBoundaryUnscale hQ))
    (.seq (moveR 217 225 id) (moveR 225 224 id))

def preparedBoundaryUnscaleCost (q N : ℕ) : ℕ :=
  generatedBoundaryUnscaleCost q N+4*N*(2*q+8)+4

theorem preparedBoundaryUnscale_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (q p : ℕ) (hpq : p ≤ q/2) (xs : List GaussianInt)
    (hbound : ∀ z ∈ xs, |gv q z.re| ≤ 8*p+1 ∧ |gv q z.im| ≤ 8*p+1)
    (v : HS 226 Q A U) (S : Stacks 226 A)
    (hleft : ∀ i, (embStk preparedBoundaryCoreReg S).L i = [])
    (hmul : ∀ i : Fin 64, (embStk preparedBoundaryCoreReg S).R (boundaryFactorMulReg i) = [])
    (hready : RsbReady (boundaryFactorState (embStk preparedBoundaryCoreReg S)) (2*q+8) q)
    (hmaster : (S.R 119).length = q)
    (h184 : S.R 184 = []) (h220 : S.R 220 = []) (h221 : S.R 221 = [])
    (h223 : S.R 223 = []) (hya : S.R 208 = []) (hac2 : S.R 215 = [])
    (hsrc : S.R 217 = cstream A (2*q+8) xs) (h225 : S.R 225 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedBoundaryUnscaleCost q xs.length ∧
      Exec (embTab preparedBoundaryCoreReg body) (preparedBoundaryUnscale hQ) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 217 []) 224
          (cstream A (2*q+8) (xs.map (unscaleBoundaryWord q))++S.R 224))}) := by
  let T := embStk preparedBoundaryCoreReg S
  let ys := xs.map (unscaleBoundaryWord q)
  have hys : ys.length = xs.length := List.length_map ..
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generatedBoundaryUnscale_exec (body := body)
    hQ hA q p hpq xs hbound (embDn preparedBoundaryCoreReg v) T hleft hmul hready
    hmaster h184 h220 h221 h223 hya hac2 hsrc
  obtain ⟨v₁',hv₁',hu₁',he₁'⟩ := exec_emb_ovr (ι := id) (body' := embTab preparedBoundaryCoreReg body)
    preparedBoundaryCoreReg_injective (fun _ => rfl) he₁ v rfl S rfl
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
    hu₃.trans (hu₂.trans (hu₁'.trans hu₁)),?_,(Exec.seq he₁'' (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · simp only [S₁,Function.update_self,h225',List.length_reverse,hsize,preparedBoundaryUnscaleCost]
    nlinarith only [hn₁]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h217' : i = 217 <;> by_cases h224 : i = 224 <;>
      by_cases h225'' : i = 225 <;>
      simp [S₂,S₁,movedR,h217',h224,h225'',h225] <;> rfl

/-- Publication retires only the native output tape; the prepared bank is otherwise unchanged. -/
theorem preparedBoundaryUnscale_project {A : ℕ} (S : Stacks 226 A)
    (output : List (Fin (A+4))) :
    embStk preparedBoundaryCoreReg
      {S with R := Function.update (Function.update S.R 217 []) 224 (output++S.R 224)} =
      {embStk preparedBoundaryCoreReg S with R :=
        (Function.update (embStk preparedBoundaryCoreReg S).R 217 [])} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  have h224 : preparedBoundaryCoreReg i ≠ 224 := (preparedBoundaryCoreReg_private i).1
  by_cases hi : i = 217
  · subst i
    simp [embStk,preparedBoundaryCoreReg]
  have h217 : preparedBoundaryCoreReg i ≠ 217 := preparedBoundaryCoreReg_injective.ne hi
  simp only [embStk,Function.comp_def,Function.update_of_ne h224,
    Function.update_of_ne h217,Function.update_of_ne hi]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
