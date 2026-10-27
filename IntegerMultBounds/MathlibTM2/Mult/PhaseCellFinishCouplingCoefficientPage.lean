module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCouplingCoefficientRow

/-! Finalize a reversed coefficient page with an executed word counter, restoring its staging suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def finishCouplingCoefficientPage : Pr P₀ 144 Q A U :=
  .seq (transferCountedLine 139 94 137 138 109 104 105) (uclear 139)

def finishCouplingCoefficientPageCost (N w : ℕ) : ℕ :=
  transferCountedLineCost N w+2*N+2

theorem finishCouplingCoefficientPage_exec (w : ℕ) (xs : List GaussianInt)
    (tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hcount : (S.R 139).length = xs.length) (hw : (S.R 94).length = w)
    (hpage : S.R 137 = (cstream A w xs).reverse++tail)
    (h109 : S.R 109 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ finishCouplingCoefficientPageCost xs.length w ∧
      Exec body finishCouplingCoefficientPage (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 137 tail)
          138 (cstream A w xs++S.R 138)) 139 [])}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := transferCountedLine_exec (body := body)
    139 94 137 138 109 104 105 (by decide) xs.length w (cstream A w xs).reverse tail
    (by simp) v S hcount hw hpage h109 h104 h105
  let S₁ : Stacks 144 A := {S with R := (Function.update (Function.update S.R 137 tail)
    138 (cstream A w xs++S.R 138))}
  have he₁' : Exec body (transferCountedLine 139 94 137 138 109 104 105)
      (mk v S) m₁ (mk v₁ S₁) := by simpa [S₁] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body 139 v₁ S₁
  refine ⟨v₂,m₁+(2*(S₁.R 139).length+2),hu₂.trans hu₁,?_,Exec.seq he₁' he₂⟩
  have hc : (S₁.R 139).length = xs.length := by simpa [S₁] using hcount
  rw [hc]
  dsimp only [finishCouplingCoefficientPageCost]
  omega

/-- Compute and finalize one retained row; later repeated-row consumers only read port 138. -/
def buildCouplingCoefficientRow : Pr P₀ 144 Q A U :=
  .seq prepareCouplingCoefficientRow (.seq (ucopy 140 139 104) finishCouplingCoefficientPage)

def buildCouplingCoefficientRowCost (P q w s t u band : ℕ) : ℕ :=
  prepareCouplingCoefficientRowCost P q w s t u band+4*(2*band+1)+4+
    finishCouplingCoefficientPageCost (2*band+1) w

theorem buildCouplingCoefficientRow_exec {P q w s t u band a b i : ℕ} [NeZero s]
    (hst : s < t) (hP : 13 ≤ P) (hi : i < s)
    (raw packetTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hrows : (S.R 140).length = 2*band+1) (h139 : S.R 139 = [])
    (hpacket : S.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band i++packetTail) :
    ∃ v' m, v'.user = v.user ∧ m ≤ buildCouplingCoefficientRowCost P q w s t u band ∧
      Exec body buildCouplingCoefficientRow (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 135
          (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++packetTail))
          138 (cstream A w (spatialCouplingCoefficientWords P q s t u band i)++S.R 138))}) := by
  let xs := spatialCouplingCoefficientWords P q s t u band i
  let next := markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++packetTail
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := prepareCouplingCoefficientRow_exec (body := body)
    hst hP hi raw packetTail v S hready hrows hpacket
  let S₁ : Stacks 144 A := {S with R := (Function.update (Function.update S.R 135 next)
    137 ((cstream A w xs).reverse++S.R 137))}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) (a := 140) (b := 139) (t := 104)
    (by decide) (by decide) (by decide) v₁ S₁
    (by simpa [S₁,embStk,groupReg] using hready.fresh 104 (by simp))
  let S₂ : Stacks 144 A := {S₁ with R := Function.update S₁.R 139 (List.replicate (2*band+1) tick)}
  have he₂' : Exec body (ucopy 140 139 104) (mk v₁ S₁) (4*(2*band+1)+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,h139,hrows] using he₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := finishCouplingCoefficientPage_exec (body := body)
    w xs (S.R 137) v₂ S₂ (by simp [S₂,xs])
    (by simpa [S₂,S₁,embStk,groupReg] using hready.width) (by simp [S₂,S₁])
    (by simpa [S₂,S₁,embStk,groupReg] using hready.fresh 109 (by simp))
    (by simpa [S₂,S₁,embStk,groupReg] using hready.fresh 104 (by simp))
    (by simpa [S₂,S₁,embStk,groupReg] using hready.fresh 105 (by simp))
  refine ⟨v₃,m₁+((4*(2*band+1)+4)+m₃),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂' he₃)).cast rfl ?_⟩
  · have hm₃' : m₃ ≤ finishCouplingCoefficientPageCost (2*band+1) w := by
      simpa only [xs,spatialCouplingCoefficientWords_length] using hm₃
    dsimp only [buildCouplingCoefficientRowCost]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h135 : k = 135 <;> by_cases h137 : k = 137 <;>
      by_cases h138 : k = 138 <;> by_cases h139k : k = 139 <;> simp_all [S₂,S₁,xs,next]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
