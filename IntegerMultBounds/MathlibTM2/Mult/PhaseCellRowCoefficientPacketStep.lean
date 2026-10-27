module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRowCoefficientFromPacket
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceBinaryPacket

/-! Generate a coefficient row and advance its retained packet to the next index. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def rowCoefficientPacketStep : Pr P₀ 117 Q A U :=
  .seq rowCoefficientFromPacket (advanceBinaryPacket 115 113 109 104 105 0)

def rowCoefficientPacketStepCost (P q V w band : ℕ) : ℕ :=
  rowCoefficientFromPacketCost P q V w band + 14*V+15

theorem rowCoefficientPacketStep_exec {P q w s t u band i : ℕ}
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hi : i < s)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = liftedCoefficientWidth P q w s t u band) (hw : (S.R 94).length = w)
    (hpacket : S.R 113 = rowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band i++tail)
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) (h106 : S.R 106 = []) (h109 : S.R 109 = [])
    (hblank : ∀ r ∈ rowCoefficientPorts, S.R r = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ rowCoefficientPacketStepCost P q (liftedCoefficientWidth P q w s t u band) w band ∧
      Exec body rowCoefficientPacketStep (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 111
          (cstream A w (spatialCouplingCoefficientWords P q s t u band i)++S.R 111)) 113
          (rowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++tail))}) := by
  let V := liftedCoefficientWidth P q w s t u band
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := rowCoefficientFromPacket_exec (body := body)
    hs0 hst hP hi tail v S hV hw hpacket h104 h105 h106 h109 hblank
  let S₁ : Stacks 117 A := {S with R := (Function.update S.R 111
    (cstream A w (spatialCouplingCoefficientWords P q s t u band i)++S.R 111))}
  let rest := (rowCoefficientPacketArguments P q s t u band i).tail.flatMap
    (fun r => binSyms V r.2) ++ tail
  obtain ⟨v₂,hu₂,he₂⟩ := advanceBinaryPacket_exec (body := body) 115 113 109 104 105 0
    (by decide) V i rest v₁ S₁ (by simpa [S₁] using hV)
    (by simpa [S₁,rest,rowCoefficientPacket,rowCoefficientPacketArguments,List.append_assoc] using hpacket)
    (by simpa [S₁] using h109) (by simpa [S₁] using h104) (by simpa [S₁] using h105)
  refine ⟨v₂,m₁+(14*V+15),hu₂.trans hu₁,?_,?_⟩
  · dsimp [rowCoefficientPacketStepCost]; dsimp only [V] at *; omega
  · simpa [rowCoefficientPacketStep,S₁,rest,rowCoefficientPacket,rowCoefficientPacketArguments,
      List.append_assoc] using Exec.seq he₁ he₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
