module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellZeroPacketSpatialCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCouplingGuard
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingCursor
public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedCouplingRow

/-! Execute one spatial row, consume its RHS, advance its source and increment its coordinate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

noncomputable def packetSpatialCouplingRowStep (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (maskedPacketSpatialCouplingRow hQ)
    (.seq (discardPrefix 94 93 104 105)
      (.seq advanceSpatialCouplingCursor (.act (.push (.rt 107) (fun _ => tick) .done))))

def packetSpatialCouplingRowStepCost (P q w s t u band : ℕ) : ℕ :=
  packetSpatialCouplingRowCost P q w s t u band+10*w+13

def packetSpatialGuardedStepCost (skip : Bool) (P q w s t u band : ℕ) : ℕ :=
  (if skip then zeroPacketSpatialCouplingRowCost P q w s t u band else packetSpatialCouplingRowCost P q w s t u band)+10*w+13

theorem packetSpatialGuardedStepCost_le (skip : Bool) (P q w s t u band : ℕ) :
    packetSpatialGuardedStepCost skip P q w s t u band ≤ packetSpatialCouplingRowStepCost P q w s t u band := by
  have hc : 10*w+10 ≤ prepareCountedCouplingInputsCost band w := by
    dsimp [prepareCountedCouplingInputsCost,copyCountedLineCost]
    nlinarith [Nat.zero_le (band*w)]
  have hz : zeroPacketSpatialCouplingRowCost P q w s t u band ≤ packetSpatialCouplingRowCost P q w s t u band := by
    dsimp [zeroPacketSpatialCouplingRowCost,packetSpatialCouplingRowCost,markedRowCoefficientCost]
    omega
  cases skip <;> simp [packetSpatialGuardedStepCost,packetSpatialCouplingRowStepCost,hz]

theorem packetSpatialCouplingRowStep_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary skip : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (tail packetTail maskTail raw : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hmask : S.R 136 = IntegerMultBounds.MathlibTM2.Layer.pairSym A skip skip::maskTail)
    (hskip : skip = true → boundary = true ∧ (i : ZMod s) ∈ haloInterior s t (2*band) a b)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hpacket : S.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band i++packetTail)
    (hsrc : S.R 141 = cstream A w ((cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band).drop i)++tail)
    (rhs : GaussianInt) (rhsTail : List (Fin (A+4)))
    (hrhs : (embStk groupReg S).R 93 = csyms A w rhs++rhsTail)
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band i, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ packetSpatialGuardedStepCost skip P q w s t u band ∧
      Exec body (packetSpatialCouplingRowStep hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update S.R 136 maskTail) 135
            (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++packetTail)) 113
            (csyms A w (couplingRowWord P q t u band a b i boundary C rhs)++S.R 113))
          93 rhsTail)
          141 (cstream A w ((cyclicPaddedLine (fun j : ZMod s =>
            if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
            then C j else 0) band).drop (i+1))++tail))
          142 ((csyms A w (if ((i : ZMod s)-(band : ZMod s)) ∈
            (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
            then C ((i : ZMod s)-(band : ZMod s)) else 0)).reverse++S.R 142))
          107 (tick::S.R 107))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩  := maskedPacketSpatialCouplingRow_exec (body := body)
    hQ boundary skip hA hw5 hqw hst hi hP C tail packetTail raw maskTail v S hmask hskip hready hpacket hsrc
    rhs rhsTail hrhs hxs has
  let z := couplingRowWord P q t u band a b i boundary C rhs
  let S₁ : Stacks 144 A := {S with R := (Function.update (Function.update (Function.update S.R 136 maskTail) 135
    (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++packetTail)) 113 (csyms A w z++S.R 113))}
  have he₁' : Exec body (maskedPacketSpatialCouplingRow hQ) (mk v S) m₁ (mk v₁ S₁) := by
    convert he₁ using 1
    apply congrArg (mk v₁)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h113 : k = 113 <;> by_cases h135 : k = 135 <;> simp_all [S₁,z,couplingRowWord]
  have hw : (S.R 94).length = w := hready.width
  have hf104 : S.R 104 = [] := hready.fresh 104 (by simp)
  have hf105 : S.R 105 = [] := hready.fresh 105 (by simp)
  have hrhs' : S.R 93 = csyms A w rhs++rhsTail := hrhs
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body)
    (count := 94) (src := 93) (trash := 104) (tmp := 105) (by decide)
    (csyms A w rhs) rhsTail v₁ S₁ (by simpa [S₁] using hrhs')
    (by simp [S₁,hw]) (by simpa [S₁] using hf104) (by simpa [S₁] using hf105)
  let S₂ : Stacks 144 A := {S₁ with R := Function.update S₁.R 93 rhsTail}
  let F := fun j : ZMod s => if j ∈
    (if boundary then haloBoundary s t band a b else haloInterior s t band a b) then C j else 0
  have hsource : S.R 141 = cstream A w ((cyclicPaddedLine F band).drop i)++tail := hsrc
  obtain ⟨v₃,hu₃,he₃⟩ := advanceSpatialCouplingCursor_exec (body := body) F band i w hi tail v₂ S₂
    (by simpa [S₂,S₁] using hw) (by simpa [S₂,S₁] using hf105)
    (by simpa [S₂,S₁] using hsource)
  let S₃ : Stacks 144 A := {S₂ with R := (Function.update (Function.update S₂.R
    141 (cstream A w ((cyclicPaddedLine F band).drop (i+1))++tail))
    142 ((csyms A w (F ((i : ZMod s)-(band : ZMod s)))).reverse++S₂.R 142))}
  have he₄ : Exec body (.act (.push (.rt 107) (fun _ => tick) .done)) (mk v₃ S₃) 1
      (mk v₃ {S₃ with R := Function.update S₃.R 107 (tick::S₃.R 107)}) := by
    simpa [Action.run,update_rt] using Exec.act (body := body)
      (.push (.rt 107) (fun _ => tick) .done) (mk v₃ S₃)
  refine ⟨v₃,m₁+((6*w+6)+((4*w+4)+1)),hu₃.trans (hu₂.trans hu₁),
    by dsimp only [packetSpatialGuardedStepCost]; omega,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ he₄))).cast (by simp) ?_⟩
  apply congrArg (mk v₃)
  simp only [S₃,S₂,S₁,z,F]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
