module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientPageLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishCouplingCoefficientPage

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def finishCouplingCoefficientInterval : Pr P₀ 144 Q A U :=
  .seq couplingCoefficientPageLoop
    (.seq (transferCountedLine 139 94 137 138 109 104 105) (uclear 135))

theorem finishCouplingCoefficientInterval_exec {P q w s t u band a b origin N : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hst : s < t) (hP : 13 ≤ P) (hN : origin+N ≤ s)
    (raw maskTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hrows : (S.R 140).length = 2*band+1) (hcount : (S.R 143).length = N)
    (hpacket : S.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band origin)
    (h139 : S.R 139 = [])
    (hmask : S.R 136 = ((couplingGuardSymbols true A s t band a b).drop origin).take N++maskTail) :
    let xs := couplingCoefficientPageInterval P q s t u band a b origin N
    ∃ v' m, v'.user = v.user ∧
      m ≤ couplingCoefficientPageIntervalLoopCost P q w s t u band a b origin N+
        transferCountedLineCost xs.length w+24*liftedCoefficientWidth P q w s t u band+4 ∧
      Exec body finishCouplingCoefficientInterval (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R
          135 []) 136 maskTail) 138 (cstream A w xs++S.R 138))
          139 (List.replicate xs.length tick)) 143 [])}) := by
  dsimp only
  let xs := couplingCoefficientPageInterval P q s t u band a b origin N
  let V := liftedCoefficientWidth P q w s t u band
  obtain ⟨vL,mL,huL,hmL,heL⟩ := couplingCoefficientPageIntervalLoop_exec (body := body)
    hA hst hP hN raw [] maskTail v S hready hrows hcount
    (by simpa using hpacket) hmask
  let L : Stacks 144 A := {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R
    135 (markedRowCoefficientPacket A V P q s t u band (origin+N)))
    136 maskTail) 137 ((cstream A w xs).reverse++S.R 137))
    139 (List.replicate xs.length tick)) 143 [])}
  have heL' : Exec body couplingCoefficientPageLoop (mk v S) mL (mk vL L) := by
    simpa [L,xs,V,h139] using heL
  obtain ⟨vF,mF,huF,hmF,heF⟩ := transferCountedLine_exec (body := body)
    139 94 137 138 109 104 105 (by decide) xs.length w (cstream A w xs).reverse (S.R 137)
    (by simp) vL L (by simp [L])
    (by simpa [L,embStk,groupReg] using hready.width) (by simp [L])
    (by simpa [L,embStk,groupReg] using hready.fresh 109 (by simp))
    (by simpa [L,embStk,groupReg] using hready.fresh 104 (by simp))
    (by simpa [L,embStk,groupReg] using hready.fresh 105 (by simp))
  let F : Stacks 144 A := {L with R := (Function.update (Function.update L.R 137 (S.R 137))
    138 (cstream A w xs++S.R 138))}
  have heF' : Exec body (transferCountedLine 139 94 137 138 109 104 105) (mk vL L) mF (mk vF F) := by
    simpa [F,L] using heF
  obtain ⟨vR,huR,heR⟩ := uclear_exec body 135 vF F
  have hpacketLen : (F.R 135).length = 12*V+1 := by simp [F,L]
  refine ⟨vR,mL+(mF+(24*V+4)),huR.trans (huF.trans huL),by dsimp only [V,xs] at *; omega,
    (Exec.seq heL' (Exec.seq heF' heR)).cast ?_ ?_⟩
  · rw [hpacketLen]; omega
  · apply congrArg (mk vR)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h135 : k = 135 <;> by_cases h136 : k = 136 <;>
      by_cases h137 : k = 137 <;> by_cases h138 : k = 138 <;>
      by_cases h139 : k = 139 <;> by_cases h143 : k = 143 <;>
      simp [F,L,xs,h135,h136,h137,h138,h139,h143]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
