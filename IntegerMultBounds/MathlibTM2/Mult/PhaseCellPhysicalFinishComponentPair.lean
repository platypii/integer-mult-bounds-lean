module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishComponentPair
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Pair the saved real result with the current imaginary result and release the saved page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 224 Q A U}

def physicalComponentReg (i : Fin 148) : Fin 224 := ⟨i.val,by omega⟩

theorem physicalComponentReg_injective : Function.Injective physicalComponentReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 224 => k.val) h)

def physicalFinishComponentPair : Pr P₀ 224 Q A U :=
  embProg physicalComponentReg Empty.elim (finishComponentPair : Pr Empty 148 Q A U)

theorem physicalFinishComponentPair_exec (hA : 4 ≤ A) (s w : ℕ) (xs ys : List GaussianInt)
    (hxlen : xs.length = s) (hylen : ys.length = s) (savedTail outputTail : List (Fin (A+4)))
    (v : HS 224 Q A U) (S : Stacks 224 A) (hcount : (S.R 131).length = s*w)
    (hx : S.R 145 = cstream A w xs++savedTail) (hy : S.R 132 = cstream A w ys++outputTail)
    (h134 : S.R 134 = []) (h140 : S.R 140 = []) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 16*s*w+14 ∧
      Exec body physicalFinishComponentPair (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 145 savedTail)
          132 (cstream A w (List.zipWith pairComponentWord xs ys)++outputTail))}) := by
  let e := physicalComponentReg
  obtain ⟨v₁,n,hu,hn,he⟩ := finishComponentPair_exec (body := Empty.elim) hA s w xs ys hxlen hylen
    savedTail outputTail (embDn e v) (embStk e S) hcount hx hy h134 h140 h147
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body) physicalComponentReg_injective
    (fun p : Empty => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let S₁ : Stacks 148 A := {embStk e S with R := Function.update (embStk e S).R 145 savedTail}
  change embOvr e ({S₁ with R := (Function.update S₁.R 132
    (cstream A w (List.zipWith pairComponentWord xs ys)++outputTail))} : Stacks 148 A).get S = _
  rw [embOvr_updR physicalComponentReg_injective]
  dsimp only [S₁]
  rw [embOvr_updR physicalComponentReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
