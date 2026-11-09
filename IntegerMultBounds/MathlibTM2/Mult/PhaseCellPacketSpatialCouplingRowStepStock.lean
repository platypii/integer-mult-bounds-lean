module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskedPacketSpatialCouplingRowStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketSpatialCouplingRowStep
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
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def packetSpatialCouplingRowStepWorkspace (K P q w s t u band : ℕ) : ℕ :=
  guardedPacketSpatialCouplingRowWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) K P q w s t u band +
    (3*(6*w+6)+(3*(4*w+4)+1))

theorem packetSpatialCouplingRowStep_exec_within (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary skip : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (tail packetTail maskTail raw : List (Fin (A+4)))
    (K : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ K)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hmask : S.R 136 = IntegerMultBounds.MathlibTM2.Layer.pairSym A skip skip::maskTail)
    (hskip : skip = couplingSkipAt boundary s t band a b i)
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
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        packetSpatialCouplingRowStepWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) K P q w s t u band) 0
        (packetSpatialCouplingRowStep hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update S.R 136 maskTail) 135
            (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++packetTail)) 113
            (csyms A w (guardedCouplingRowWord P q t u band a b i boundary C rhs)++S.R 113))
          93 rhsTail)
          141 (cstream A w ((cyclicPaddedLine (fun j : ZMod s =>
            if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
            then C j else 0) band).drop (i+1))++tail))
          142 ((csyms A w (if ((i : ZMod s)-(band : ZMod s)) ∈
            (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
            then C ((i : ZMod s)-(band : ZMod s)) else 0)).reverse++S.R 142))
          107 (tick::S.R 107))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩  := maskedPacketSpatialCouplingRow_exec_within (body := body)
    hQ boundary skip hA hw5 hqw hst hi hP C tail packetTail raw maskTail K hpush v S hmask hskip hready hpacket hsrc
    rhs rhsTail hrhs hxs has
  let z := guardedCouplingRowWord P q t u band a b i boundary C rhs
  let S₁ : Stacks 144 A := {S with R := (Function.update (Function.update (Function.update S.R 136 maskTail) 135
    (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++packetTail)) 113 (csyms A w z++S.R 113))}
  have he₁' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
      guardedPacketSpatialCouplingRowWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) K P q w s t u band) 0
      (maskedPacketSpatialCouplingRow hQ) (mk v S) m₁ (mk v₁ S₁) := by
    convert he₁ using 1
    apply congrArg (mk v₁)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h113 : k = 113 <;> by_cases h135 : k = 135 <;> simp_all [S₁,z,guardedCouplingRowWord]
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
  have ht₂ := mn_native_exec_within he₂ 3 (by
    simp [discardPrefix, transfer, transferAct, uclear, moveR, whileR,
      scanR, drainR, popDo, keepIn, pushN, moveStep, peekR, mnNativePushBound, mnActPush])
    0 _ (Nat.le_refl _)
  have ht₃ := mn_native_exec_within he₃ 3 (by
    simp [advanceSpatialCouplingCursor, transfer, transferAct, scanR, drainR,
      popDo, keepIn, pushN, moveR, moveStep, whileR, peekR, mnNativePushBound, mnActPush])
    0 _ (Nat.le_refl _)
  have ht₄ := mn_native_exec_within he₄ 1 (by change 1 ≤ 1; exact le_refl _)
    0 (mnSize (mk v₃ S₃)+0+1) (by omega)
  have ht := mn_seq_within_add he₁' (mn_seq_within_add ht₂ (mn_seq_within_add ht₃ ht₄))
  refine ⟨v₃,m₁+((6*w+6)+((4*w+4)+1)),hu₃.trans (hu₂.trans hu₁),
    by dsimp only [packetSpatialGuardedStepCost]; omega,
    (ht.mono (by
      intro d z hz
      dsimp only [packetSpatialCouplingRowStepWorkspace]
      simp only [csyms,IntegerMultBounds.MathlibTM2.Layer.length_coeffSyms] at hz
      omega)).cast (by simp) ?_⟩
  apply congrArg (mk v₃)
  simp only [S₃,S₂,S₁,z,F]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
