module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRowCoefficientPacketStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishMarkedWidth

/-! A self-describing retained coefficient packet releases its width scratch between rows. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def markedRowCoefficientPacket (A V P q s t u band i : ℕ) : List (Fin (A+4)) :=
  List.replicate V tick++bitSymbol false::rowCoefficientPacket A V P q s t u band i

@[simp] theorem markedRowCoefficientPacket_length (A V P q s t u band i : ℕ) :
    (markedRowCoefficientPacket A V P q s t u band i).length = 8*V+1 := by
  simp [markedRowCoefficientPacket]; omega

def markedRowCoefficient : Pr P₀ 117 Q A U :=
  .seq (takeMarkedWidth 113 115)
    (.seq rowCoefficientPacketStep (publishMarkedWidth 115 113 105))

def markedRowCoefficientCost (P q V w band : ℕ) : ℕ :=
  rowCoefficientFromPacketCost P q V w band + 22*V+25

theorem markedRowCoefficient_exec {P q w s t u band i : ℕ}
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hi : i < s)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (h115 : S.R 115 = []) (hw : (S.R 94).length = w)
    (hpacket : S.R 113 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band i++tail)
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) (h106 : S.R 106 = []) (h109 : S.R 109 = [])
    (hblank : ∀ r ∈ rowCoefficientPorts, S.R r = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ markedRowCoefficientCost P q (liftedCoefficientWidth P q w s t u band) w band ∧
      Exec body markedRowCoefficient (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 111
          (cstream A w (spatialCouplingCoefficientWords P q s t u band i)++S.R 111)) 113
          (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++tail))}) := by
  let V := liftedCoefficientWidth P q w s t u band
  let packet := rowCoefficientPacket A V P q s t u band i++tail
  obtain ⟨v₁,hu₁,he₁⟩ := takeMarkedWidth_exec (body := body) 113 115 (by decide) V packet v S
    (by simpa [packet,V,markedRowCoefficientPacket,List.append_assoc] using hpacket)
  let S₁ : Stacks 117 A := {S with R := (Function.update (Function.update S.R 113 packet)
    115 (List.replicate V tick++S.R 115))}
  have hoff₁ (r : Fin 117) (h113 : r ≠ 113) (h115 : r ≠ 115) : S₁.R r = S.R r := by
    simp [S₁,h113,h115]
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := rowCoefficientPacketStep_exec (body := body) (P := P) (q := q) (w := w)
    (s := s) (t := t) (u := u) (band := band) (i := i)
    hs0 hst hP hi tail v₁ S₁ (by simp [S₁,h115,V])
    (by simpa [S₁] using hw) (by simp [S₁,packet,V])
    (by simpa [S₁] using h104) (by simpa [S₁] using h105)
    (by simpa [S₁] using h106) (by simpa [S₁] using h109) (by
      intro r hr
      have h113 : r ≠ 113 := by intro h; subst r; simp at hr
      have h115 : r ≠ 115 := by intro h; subst r; simp at hr
      rw [hoff₁ r h113 h115]; exact hblank r hr)
  let S₂ : Stacks 117 A := {S₁ with R := (Function.update (Function.update S₁.R 111
    (cstream A w (spatialCouplingCoefficientWords P q s t u band i)++S₁.R 111)) 113
    (rowCoefficientPacket A V P q s t u band (i+1)++tail))}
  obtain ⟨v₃,hu₃,he₃⟩ := publishMarkedWidth_exec (body := body) 115 113 105 (by decide) v₂ S₂
    (by simpa [S₂,S₁] using h105)
  have hlen : (S₂.R 115).length = V := by simp [S₂,S₁,h115]
  refine ⟨v₃,(2*V+3)+(m₂+(6*(S₂.R 115).length+7)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [hlen]; dsimp [markedRowCoefficientCost,rowCoefficientPacketStepCost] at *
    dsimp only [V] at *; omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases h113 : r = 113 <;> by_cases h111 : r = 111 <;> by_cases hr115 : r = 115 <;>
      simp_all [S₂,S₁,V,markedRowCoefficientPacket,List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
