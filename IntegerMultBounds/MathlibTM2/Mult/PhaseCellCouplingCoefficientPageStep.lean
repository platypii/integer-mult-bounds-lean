module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientPageRow

/-! Consume the actual guard stream while generating a sparse coefficient page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def couplingCoefficientPageStep : Pr P₀ 144 Q A U :=
  .seq (.act (.pop (.rt 136) (fun v o => {v with flag := pairRe (o.getD blank)}) .done))
    couplingCoefficientPageRow

theorem couplingCoefficientPageStep_exec {P q w s t u band a b i : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hst : s < t) (hP : 13 ≤ P) (hi : i < s)
    (raw packetTail maskTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hrows : (S.R 140).length = 2*band+1)
    (hpacket : S.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band i++packetTail)
    (hmask : S.R 136 = pairSym A (couplingSkipAt true s t band a b i)
      (couplingSkipAt true s t band a b i)::maskTail) :
    let xs := couplingCoefficientPageChunk P q s t u band a b i
    ∃ v' m, v'.user = v.user ∧
      m ≤ couplingCoefficientPageRowCost (couplingSkipAt true s t band a b i) P q w s t u band+1 ∧
      Exec body couplingCoefficientPageStep (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R 136 maskTail) 135
          (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++packetTail))
          137 ((cstream A w xs).reverse++S.R 137)) 139 (List.replicate xs.length tick++S.R 139))}) := by
  dsimp only
  let skip := couplingSkipAt true s t band a b i
  let S₀ : Stacks 144 A := {S with R := Function.update S.R 136 maskTail}
  let v₀ : HS 144 Q A U := {v with flag := skip}
  have he₀ : Exec body (.act (.pop (.rt 136) (fun v o => {v with flag := pairRe (o.getD blank)}) .done))
      (mk v S) 1 (mk v₀ S₀) := by
    simpa [S₀,v₀,skip,Action.run,update_rt,hmask,pairRe_pairSym hA] using
      Exec.act (body := body) (.pop (.rt 136) (fun v o => {v with flag := pairRe (o.getD blank)}) .done) (mk v S)
  have hready₀ : CouplingReady P q w s t u band a b raw (embStk groupReg S₀) := by
    rw [show embStk groupReg S₀ = embStk groupReg S from groupProject_updateR S 136 _ (by decide)]
    exact hready
  obtain ⟨v',m,hu,hm,he⟩ := couplingCoefficientPageRow_exec (body := body) skip hst hP hi
    raw packetTail v₀ S₀ rfl hready₀ (by simpa [S₀] using hrows) (by simpa [S₀] using hpacket)
  exact ⟨v',1+m,hu,by dsimp only [skip] at hm; omega,(Exec.seq he₀ he)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
