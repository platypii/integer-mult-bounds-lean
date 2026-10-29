module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishCouplingCoefficientInterval
public import IntegerMultBounds.MathlibTM2.Host.Embed

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellRationalArgs
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

def intervalPageReg (i : Fin 144) : Fin 168 := ⟨i.val,by omega⟩

theorem intervalPageReg_injective : Function.Injective intervalPageReg := by
  intro i j he
  have hv := congrArg (fun k : Fin 168 => k.val) he
  exact Fin.ext hv

/-- Private page controls and binary metadata do not alter the arithmetic view. -/
theorem intervalPageCore_updateR (S : Stacks 168 A) (k : Fin 168) (hk : 117 ≤ k.val)
    (xs : List (Fin (A+4))) :
    embStk groupReg (embStk intervalPageReg {S with R := Function.update S.R k xs}) =
      embStk groupReg (embStk intervalPageReg S) := by
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  have hne : intervalPageReg (groupReg r) ≠ k := by
    intro he
    have hv := congrArg (fun j : Fin 168 => j.val) he
    change r.val = k.val at hv
    have hr := r.isLt
    omega
  simp only [embStk,Function.comp_def,Function.update_of_ne hne]

def placedFinishCouplingCoefficientInterval : Pr P₀ 168 Q A U :=
  embProg intervalPageReg Empty.elim (finishCouplingCoefficientInterval (P₀ := Empty))

theorem placedFinishCouplingCoefficientInterval_exec {P q w s t u band a b origin N : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hst : s < t) (hP : 13 ≤ P) (hN : origin+N ≤ s)
    (raw maskTail : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg (embStk intervalPageReg S)))
    (hrows : (S.R 140).length = 2*band+1) (hcount : (S.R 143).length = N)
    (hpacket : S.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band origin)
    (h139 : S.R 139 = [])
    (hmask : S.R 136 = ((couplingGuardSymbols true A s t band a b).drop origin).take N++maskTail) :
    let xs := couplingCoefficientPageInterval P q s t u band a b origin N
    ∃ v' m, v'.user = v.user ∧
      m ≤ couplingCoefficientPageIntervalLoopCost P q w s t u band a b origin N+
        transferCountedLineCost xs.length w+24*liftedCoefficientWidth P q w s t u band+4 ∧
      Exec body placedFinishCouplingCoefficientInterval (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R
          135 []) 136 maskTail) 138 (cstream A w xs++S.R 138))
          139 (List.replicate xs.length tick)) 143 [])}) := by
  dsimp only
  let xs := couplingCoefficientPageInterval P q s t u band a b origin N
  obtain ⟨v₁,m,hu₁,hm,he⟩ := finishCouplingCoefficientInterval_exec
    (body := fun p : Empty => nomatch p) hA hst hP hN raw maskTail
    (embDn intervalPageReg v) (embStk intervalPageReg S) hready hrows hcount hpacket h139 hmask
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    intervalPageReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let T := embStk intervalPageReg S
  let T₁ : Stacks 144 A := {T with R := Function.update T.R 135 []}
  let T₂ : Stacks 144 A := {T₁ with R := Function.update T₁.R 136 maskTail}
  let T₃ : Stacks 144 A := {T₂ with R := Function.update T₂.R 138 (cstream A w xs++T.R 138)}
  let T₄ : Stacks 144 A := {T₃ with R := Function.update T₃.R 139 (List.replicate xs.length tick)}
  change embOvr intervalPageReg ({T₄ with R := Function.update T₄.R 143 []} : Stacks 144 A).get S = _
  rw [embOvr_updR intervalPageReg_injective T₄ S 143,
    embOvr_updR intervalPageReg_injective T₃ S 139,
    embOvr_updR intervalPageReg_injective T₂ S 138,
    embOvr_updR intervalPageReg_injective T₁ S 136,
    embOvr_updR intervalPageReg_injective T S 135,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
