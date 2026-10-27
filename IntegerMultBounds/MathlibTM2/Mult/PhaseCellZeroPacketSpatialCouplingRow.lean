module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceMarkedBinaryPacket
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketSpatialCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryGuardSemantics
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingRowValue

/-! Skip coefficient generation and arithmetic for certified zero coupling rows. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def zeroPacketSpatialCouplingRow : Pr P₀ 144 Q A U :=
  .seq (advanceMarkedBinaryPacket 115 135 109 104 105 0) (copyPrefix 94 93 113 104 105)

def zeroPacketSpatialCouplingRowCost (P q w s t u band : ℕ) : ℕ :=
  22*liftedCoefficientWidth P q w s t u band+10*w+35

theorem zeroPacketSpatialCouplingRow_exec {P q w s t u band a b i : ℕ}
    (raw packetTail rhsTail : List (Fin (A+4))) (rhs : GaussianInt)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hpacket : S.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band i++packetTail)
    (hrhs : S.R 93 = csyms A w rhs++rhsTail) :
    ∃ v', v'.user = v.user ∧
      Exec body zeroPacketSpatialCouplingRow (mk v S) (zeroPacketSpatialCouplingRowCost P q w s t u band)
        (mk v' {S with R := (Function.update (Function.update S.R 113 (csyms A w rhs++S.R 113)) 135
          (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++packetTail))}) := by
  let V := liftedCoefficientWidth P q w s t u band
  let rest := (preparedRowPacketArguments P q s t u band i).tail.flatMap (fun r => binSyms V r.2)++packetTail
  obtain ⟨v₁,hu₁,he₁⟩ := advanceMarkedBinaryPacket_exec (body := body) 115 135 109 104 105 0
    (by decide) V i rest v S (hready.fresh 115 (by simp))
    (by simpa [markedRowCoefficientPacket,preparedRowPacket,preparedRowPacketArguments,rest,List.append_assoc] using hpacket)
    (hready.fresh 109 (by simp)) (hready.fresh 104 (by simp)) (hready.fresh 105 (by simp))
  let S₁ : Stacks 144 A := {S with R := (Function.update S.R 135
    (markedRowCoefficientPacket A V P q s t u band (i+1)++packetTail))}
  have he₁' : Exec body (advanceMarkedBinaryPacket 115 135 109 104 105 0) (mk v S) (22*V+25)
      (mk v₁ S₁) := by
    simpa [S₁,markedRowCoefficientPacket,preparedRowPacket,preparedRowPacketArguments,rest,List.append_assoc] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := copyPrefix_exec (body := body) (count := 94) (src := 93) (dst := 113)
    (saved := 104) (tmp := 105) (by decide) v₁ S₁ (csyms A w rhs) rhsTail
    (by simpa [S₁] using hrhs) (by simpa [S₁,embStk,groupReg] using hready.width)
    (by simpa [S₁,embStk,groupReg] using hready.fresh 104 (by simp)) (by simpa [S₁,embStk,groupReg] using hready.fresh 105 (by simp))
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' he₂).cast ?_ ?_⟩
  · simp [zeroPacketSpatialCouplingRowCost,V]; omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h113 : k = 113 <;> by_cases h135 : k = 135 <;> simp_all [S₁,V]

noncomputable def guardedPacketSpatialCouplingRow (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .cond (·.flag) zeroPacketSpatialCouplingRow (packetSpatialCouplingRow hQ)

theorem guardedPacketSpatialCouplingRow_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary skip : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (tail packetTail raw : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A) (hflag : v.flag = skip)
    (hskip : skip = couplingSkipAt boundary s t band a b i)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hpacket : S.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band i++packetTail)
    (hsrc : S.R 141 = cstream A w ((cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band).drop i)++tail)
    (rhs : GaussianInt) (rhsTail : List (Fin (A+4))) (hrhs : S.R 93 = csyms A w rhs++rhsTail)
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band i, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (if skip then zeroPacketSpatialCouplingRowCost P q w s t u band else packetSpatialCouplingRowCost P q w s t u band)+1 ∧
      Exec body (guardedPacketSpatialCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 113
          (csyms A w (guardedCouplingRowWord P q t u band a b i boundary C rhs)++S.R 113)) 135
          (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++packetTail))}) := by
  cases skip with
  | true =>
    obtain ⟨v',hu,he⟩ := zeroPacketSpatialCouplingRow_exec (body := body) raw packetTail rhsTail rhs v S hready hpacket hrhs
    refine ⟨v',zeroPacketSpatialCouplingRowCost P q w s t u band+1,hu,by simp,?_⟩
    simp only [guardedCouplingRowWord,← hskip,ite_true]
    exact Exec.cond_true hflag he
  | false =>
    obtain ⟨v',m,hu,hm,he⟩ := packetSpatialCouplingRow_exec (body := body)
      hQ boundary hA hw5 hqw hst hi hP C tail packetTail raw v S hready hpacket hsrc rhs rhsTail hrhs hxs has
    exact ⟨v',m+1,hu,by simpa using Nat.add_le_add_right hm 1,by
      simp only [guardedCouplingRowWord,← hskip,Bool.false_eq_true,ite_false]
      exact Exec.cond_false hflag he⟩

noncomputable def maskedPacketSpatialCouplingRow (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (.act (.pop (.rt 136) (fun v o => {v with flag := pairRe (o.getD blank)}) .done))
    (guardedPacketSpatialCouplingRow hQ)

theorem maskedPacketSpatialCouplingRow_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary skip : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (tail packetTail raw : List (Fin (A+4)))
    (maskTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hmask : S.R 136 = pairSym A skip skip::maskTail)
    (hskip : skip = couplingSkipAt boundary s t band a b i)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hpacket : S.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band i++packetTail)
    (hsrc : S.R 141 = cstream A w ((cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band).drop i)++tail)
    (rhs : GaussianInt) (rhsTail : List (Fin (A+4))) (hrhs : S.R 93 = csyms A w rhs++rhsTail)
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band i, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (if skip then zeroPacketSpatialCouplingRowCost P q w s t u band else packetSpatialCouplingRowCost P q w s t u band)+2 ∧
      Exec body (maskedPacketSpatialCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 136 maskTail) 113
          (csyms A w (guardedCouplingRowWord P q t u band a b i boundary C rhs)++S.R 113)) 135
          (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++packetTail))}) := by
  let S₀ : Stacks 144 A := {S with R := Function.update S.R 136 maskTail}
  let v₀ : HS 144 Q A U := {v with flag := skip}
  have he₀ : Exec body (.act (.pop (.rt 136) (fun v o => {v with flag := pairRe (o.getD blank)}) .done))
      (mk v S) 1 (mk v₀ S₀) := by
    simpa [S₀,v₀,Action.run,update_rt,hmask,pairRe_pairSym (show 4 ≤ A by omega)] using
      Exec.act (body := body) (.pop (.rt 136) (fun v o => {v with flag := pairRe (o.getD blank)}) .done) (mk v S)
  have hready₀ : CouplingReady P q w s t u band a b raw (embStk groupReg S₀) := by
    rw [show embStk groupReg S₀ = embStk groupReg S from groupProject_updateR S 136 _ (by decide)]
    exact hready
  obtain ⟨v',m,hu,hm,he⟩ := guardedPacketSpatialCouplingRow_exec (body := body)
    hQ boundary skip hA hw5 hqw hst hi hP C tail packetTail raw v₀ S₀ rfl hskip hready₀
    (by simpa [S₀] using hpacket) (by simpa [S₀] using hsrc) rhs rhsTail
    (by simpa [S₀] using hrhs) hxs has
  refine ⟨v',1+m,hu,by omega,(Exec.seq he₀ he).cast rfl ?_⟩
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
