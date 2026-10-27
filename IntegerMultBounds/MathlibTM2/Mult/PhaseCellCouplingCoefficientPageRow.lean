module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCouplingCoefficientRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceMarkedBinaryPacket
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientPageData

/-! Generate or skip one page row, advancing its packet and counting every emitted word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def couplingCoefficientPageRow : Pr P₀ 144 Q A U :=
  .cond (·.flag) (advanceMarkedBinaryPacket 115 135 109 104 105 0)
    (.seq prepareCouplingCoefficientRow (ucopy 140 139 104))

def couplingCoefficientPageRowCost (skip : Bool) (P q w s t u band : ℕ) : ℕ :=
  (if skip then 22*liftedCoefficientWidth P q w s t u band+25 else
    prepareCouplingCoefficientRowCost P q w s t u band+4*(2*band+1)+4)+1

theorem couplingCoefficientPageRow_exec {P q w s t u band a b i : ℕ} [NeZero s]
    (skip : Bool) (hst : s < t) (hP : 13 ≤ P) (hi : i < s)
    (raw packetTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hflag : v.flag = skip)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hrows : (S.R 140).length = 2*band+1)
    (hpacket : S.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band i++packetTail) :
    let xs := if skip then [] else spatialCouplingCoefficientWords P q s t u band i
    ∃ v' m, v'.user = v.user ∧ m ≤ couplingCoefficientPageRowCost skip P q w s t u band ∧
      Exec body couplingCoefficientPageRow (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 135
          (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++packetTail))
          137 ((cstream A w xs).reverse++S.R 137)) 139 (List.replicate xs.length tick++S.R 139))}) := by
  dsimp only
  cases skip with
  | true =>
    let V := liftedCoefficientWidth P q w s t u band
    let rest := (preparedRowPacketArguments P q s t u band i).tail.flatMap (fun r => binSyms V r.2)++packetTail
    obtain ⟨v',hu,he⟩ := advanceMarkedBinaryPacket_exec (body := body) 115 135 109 104 105 0
      (by decide) V i rest v S (hready.fresh 115 (by simp))
      (by simpa [markedRowCoefficientPacket,preparedRowPacket,preparedRowPacketArguments,rest,List.append_assoc] using hpacket)
      (hready.fresh 109 (by simp)) (hready.fresh 104 (by simp)) (hready.fresh 105 (by simp))
    refine ⟨v',22*V+26,hu,by simp [couplingCoefficientPageRowCost,V],?_⟩
    have he' : Exec body (advanceMarkedBinaryPacket 115 135 109 104 105 0) (mk v S) (22*V+25)
        (mk v' {S with R := (Function.update S.R 135
          (markedRowCoefficientPacket A V P q s t u band (i+1)++packetTail))}) := by
      simpa [rest,markedRowCoefficientPacket,preparedRowPacket,preparedRowPacketArguments,List.append_assoc] using he
    simp only [ite_true,cstream_nil,List.reverse_nil,List.nil_append,List.length_nil,List.replicate_zero]
    refine (Exec.cond_true hflag he').cast (by omega) ?_
    apply congrArg (mk v')
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h135 : k = 135 <;> by_cases h137 : k = 137 <;> by_cases h139 : k = 139 <;>
      simp_all [V]
  | false =>
    let xs := spatialCouplingCoefficientWords P q s t u band i
    let next := markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++packetTail
    obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := prepareCouplingCoefficientRow_exec (body := body)
      hst hP hi raw packetTail v S hready hrows hpacket
    let S₁ : Stacks 144 A := {S with R := (Function.update (Function.update S.R 135 next)
      137 ((cstream A w xs).reverse++S.R 137))}
    obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) (a := 140) (b := 139) (t := 104)
      (by decide) (by decide) (by decide) v₁ S₁
      (by simpa [S₁,embStk,groupReg] using hready.fresh 104 (by simp))
    refine ⟨v₂,(m₁+(4*(2*band+1)+4))+1,hu₂.trans hu₁,?_,?_⟩
    · dsimp only [couplingCoefficientPageRowCost]; simp only [Bool.false_eq_true,ite_false]; omega
    · have he₂' : Exec body (ucopy 140 139 104) (mk v₁ S₁) (4*(2*band+1)+4)
          (mk v₂ {S₁ with R := Function.update S₁.R 139 (List.replicate (2*band+1) tick++S.R 139)}) := by
        simpa [S₁,hrows] using he₂
      simpa [couplingCoefficientPageRow,S₁,xs,next] using
        Exec.cond_false (p := advanceMarkedBinaryPacket 115 135 109 104 105 0) hflag (Exec.seq he₁ he₂')

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
