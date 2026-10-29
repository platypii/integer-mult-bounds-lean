module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFinishCouplingCoefficientInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingPacket

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

def placedPrepareCouplingIntervalPacket : Pr P₀ 168 Q A U :=
  embProg intervalPageReg Empty.elim (prepareRetainedCouplingPacket (P₀ := Empty))

theorem placedPrepareCouplingIntervalPacket_exec {P q w s t u band a b origin : ℕ}
    (hP : 13 ≤ P) (hiRow : origin < s)
    (raw : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : CouplingReady P q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg S)))
    (hi : (S.R 107).length = origin) :
    ∃ v' m, v'.user = v.user ∧ m ≤ buildMarkedRowCoefficientPacketCost P q w s t u band origin ∧
      Exec body placedPrepareCouplingIntervalPacket (mk v S) m
        (mk v' {S with R := (Function.update S.R 135
          (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band)
            P q s t u band origin++S.R 135))}) := by
  obtain ⟨v₁,m,hu₁,hm,he⟩ := prepareRetainedCouplingPacket_exec
    (body := fun p : Empty => nomatch p) hP hiRow raw
    (embDn intervalPageReg v) (embStk intervalPageReg S) hready hi
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    intervalPageReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [embOvr_updR intervalPageReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
