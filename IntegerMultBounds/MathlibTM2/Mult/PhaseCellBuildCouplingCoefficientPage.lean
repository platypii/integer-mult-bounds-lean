module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientPageLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCouplingPageCounts
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishCouplingCoefficientPage

/-! Generate a complete sparse coefficient page from ordinary headers, retaining its page, word count and row width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def buildCouplingCoefficientPage : Pr P₀ 144 Q A U :=
  .seq (prepareCouplingGuard true) (.seq prepareRetainedCouplingPacket
    (.seq prepareCouplingPageCounts (.seq couplingCoefficientPageLoop
      (.seq (transferCountedLine 139 94 137 138 109 104 105) (uclear 135)))))

def buildCouplingCoefficientPageCost (P q w s t u band a b : ℕ) : ℕ :=
  prepareCouplingGuardCost s t band a b+buildMarkedRowCoefficientPacketCost P q w s t u band 0+
    prepareCouplingPageCountsCost s band+couplingCoefficientPageLoopCost P q w s t u band a b s+
    transferCountedLineCost (couplingCoefficientPage P q s t u band a b s).length w+
    24*liftedCoefficientWidth P q w s t u band+4

theorem buildCouplingCoefficientPage_exec {P q w s t u band a b : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hst : s < t) (hP : 13 ≤ P) (ha : a ≤ s) (hb : b ≤ s)
    (raw : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hindex : S.R 107 = []) (h135 : S.R 135 = []) (h139 : S.R 139 = [])
    (h140 : S.R 140 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ buildCouplingCoefficientPageCost P q w s t u band a b ∧
      Exec body buildCouplingCoefficientPage (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 138
          (cstream A w (couplingCoefficientPage P q s t u band a b s)++S.R 138))
          139 (List.replicate (couplingCoefficientPage P q s t u band a b s).length tick)) 140 (List.replicate (2*band+1) tick))}) := by
  let V := liftedCoefficientWidth P q w s t u band
  let xs := couplingCoefficientPage P q s t u band a b s
  obtain ⟨vG,mG,huG,hmG,heG⟩ := prepareCouplingGuard_exec (body := body) true hst ha hb hA raw v S hready
  let G : Stacks 144 A := {S with R := Function.update S.R 136 (couplingGuardSymbols true A s t band a b++S.R 136)}
  have hreadyG : CouplingReady P q w s t u band a b raw (embStk groupReg G) := by
    rw [show embStk groupReg G = embStk groupReg S from groupProject_updateR S 136 _ (by decide)]
    exact hready
  obtain ⟨vP,mP,huP,hmP,heP⟩ := prepareRetainedCouplingPacket_exec (body := body)
    (i := 0) hP (NeZero.pos s) raw vG G hreadyG (by simpa [G,hindex])
  let B : Stacks 144 A := {G with R := Function.update G.R 135 (markedRowCoefficientPacket A V P q s t u band 0++S.R 135)}
  have hreadyB : CouplingReady P q w s t u band a b raw (embStk groupReg B) := by
    rw [show embStk groupReg B = embStk groupReg G from groupProject_updateR G 135 _ (by decide)]
    exact hreadyG
  obtain ⟨vC,huC,heC⟩ := prepareCouplingPageCounts_exec (body := body) s band vP B
    (by simpa [B,G,embStk,groupReg] using hready.axis)
    (by simpa [B,G,embStk,groupReg] using hready.bandwidth)
    (by simpa [B,G] using h140) (by simpa [B,G] using h143)
    (by simpa [B,G,embStk,groupReg] using hready.fresh 109 (by simp))
    (by simpa [B,G,embStk,groupReg] using hready.fresh 104 (by simp))
  let C : Stacks 144 A := {B with R := (Function.update (Function.update B.R 140 (List.replicate (2*band+1) tick))
    143 (List.replicate s tick))}
  have hreadyC : CouplingReady P q w s t u band a b raw (embStk groupReg C) := by
    dsimp only [C]
    rw [groupProject_updateR ({B with R := Function.update B.R 140 (List.replicate (2*band+1) tick)} : Stacks 144 A)
      143 (List.replicate s tick) (by decide),groupProject_updateR B 140 _ (by decide)]
    exact hreadyB
  obtain ⟨vL,mL,huL,hmL,heL⟩ := couplingCoefficientPageLoop_exec (body := body)
    hA hst hP le_rfl raw (S.R 135) (S.R 136) vC C hreadyC (by simp [C]) (by simp [C])
    (by simp [C,B,V]) (by simp [C,B,G])
  let L : Stacks 144 A := {C with R := (Function.update (Function.update (Function.update (Function.update (Function.update C.R
    135 (markedRowCoefficientPacket A V P q s t u band s++S.R 135))
    136 (S.R 136)) 137 ((cstream A w xs).reverse++S.R 137))
    139 (List.replicate xs.length tick++S.R 139)) 143 [])}
  obtain ⟨vF,mF,huF,hmF,heF⟩ := transferCountedLine_exec (body := body)
    139 94 137 138 109 104 105 (by decide) xs.length w (cstream A w xs).reverse (S.R 137)
    (by simp) vL L (by simp [L,h139])
    (by simpa [L,C,B,G,embStk,groupReg] using hready.width) (by simp [L])
    (by simpa [L,C,B,G,embStk,groupReg] using hready.fresh 109 (by simp))
    (by simpa [L,C,B,G,embStk,groupReg] using hready.fresh 104 (by simp))
    (by simpa [L,C,B,G,embStk,groupReg] using hready.fresh 105 (by simp))
  let F : Stacks 144 A := {L with R := (Function.update (Function.update L.R 137 (S.R 137))
    138 (cstream A w xs++S.R 138))}
  obtain ⟨vR,huR,heR⟩ := uclear_exec body 135 vF F
  have hpacketLen : (F.R 135).length = 12*V+1 := by simp [F,L,h135]
  have heL' : Exec body couplingCoefficientPageLoop (mk vC C) mL (mk vL L) := by
    simpa [L,C,B,G,xs,V] using heL
  have heF' : Exec body (transferCountedLine 139 94 137 138 109 104 105) (mk vL L) mF (mk vF F) := by
    simpa [F,L,C,B,G] using heF
  refine ⟨vR,mG+(mP+(prepareCouplingPageCountsCost s band+(mL+(mF+(24*V+4))))),
    huR.trans (huF.trans (huL.trans (huC.trans (huP.trans huG)))),?_,
    (Exec.seq heG (Exec.seq heP (Exec.seq heC (Exec.seq heL' (Exec.seq heF' heR))))).cast ?_ ?_⟩
  · dsimp only [buildCouplingCoefficientPageCost]
    dsimp only [xs,V] at hmF ⊢
    omega
  · rw [hpacketLen]; omega
  · apply congrArg (mk vR)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h138 : k = 138
    · subst k; simp [F,L,C,B,G,xs]
    by_cases h140k : k = 140
    · subst k; simp [F,L,C,B,G]
    by_cases h135k : k = 135
    · subst k; simp [F,L,C,B,G,h135]
    by_cases h136 : k = 136
    · subst k; simp [F,L,C,B,G]
    by_cases h137 : k = 137
    · subst k; simp [F,L,C,B,G]
    by_cases h139k : k = 139
    · subst k; simp [F,L,C,B,G,h139,xs]
    by_cases h143k : k = 143
    · subst k; simp [F,L,C,B,G,h143]
    simp [F,L,C,B,G,h138,h140k,h135k,h136,h137,h139k,h143k]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
