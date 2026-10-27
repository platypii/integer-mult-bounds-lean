module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingPacket
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTransferCountedLine

/-! Execute one coefficient-page row during setup, retaining its exact reversed symbols. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def prepareCouplingCoefficientRow : Pr P₀ 144 Q A U :=
  .seq retainedCouplingCoefficients (transferCountedLine 140 94 111 137 109 104 105)

def prepareCouplingCoefficientRowCost (P q w s t u band : ℕ) : ℕ :=
  markedRowCoefficientCost P q (liftedCoefficientWidth P q w s t u band) w band+
    transferCountedLineCost (2*band+1) w

theorem prepareCouplingCoefficientRow_exec {P q w s t u band a b i : ℕ} [NeZero s]
    (hst : s < t) (hP : 13 ≤ P) (hi : i < s)
    (raw packetTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hrows : (S.R 140).length = 2*band+1)
    (hpacket : S.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band i++packetTail) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCouplingCoefficientRowCost P q w s t u band ∧
      Exec body prepareCouplingCoefficientRow (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 135
          (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++packetTail))
          137 ((cstream A w (spatialCouplingCoefficientWords P q s t u band i)).reverse++S.R 137))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := retainedCouplingCoefficients_exec (body := body)
    hst hP hi raw packetTail v S hready hpacket
  let xs := cstream A w (spatialCouplingCoefficientWords P q s t u band i)
  let next := markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++packetTail
  let S₁ : Stacks 144 A := {S with R := Function.update (Function.update S.R 111 (xs++S.R 111)) 135 next}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := transferCountedLine_exec (body := body)
    140 94 111 137 109 104 105 (by decide) (2*band+1) w xs (S.R 111)
    (by simp [xs]) v₁ S₁ (by simpa [S₁] using hrows)
    (by simpa [S₁,embStk,groupReg] using hready.width) (by simp [S₁])
    (by simpa [S₁,embStk,groupReg] using hready.fresh 109 (by simp))
    (by simpa [S₁,embStk,groupReg] using hready.fresh 104 (by simp))
    (by simpa [S₁,embStk,groupReg] using hready.fresh 105 (by simp))
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h111 : k = 111 <;> by_cases h135 : k = 135 <;> by_cases h137 : k = 137 <;>
    simp_all [S₁,xs,next]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
