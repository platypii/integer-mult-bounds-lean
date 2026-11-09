module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunPreparedPacketCouplingRowsStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunSpatialCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReversePrefixInPlace

/-! Generate the whole-line row clock, execute every coupling row and publish
in natural coordinate order, releasing the clock and current index. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

@[irreducible] def couplingGuardPush : ℕ :=
  mnProgPush (generateRecoveryCouplingMask (P₀ := Empty) (Q := Q) (A := A) (U := U) true)

@[irreducible] def retainedCouplingPacketPush : ℕ :=
  mnProgPush (buildMarkedRowCoefficientPacket (P₀ := Empty) (Q := Q) (A := A) (U := U))

theorem prepareCouplingGuard_native (boundary : Bool) :
    mnNativePushBound (couplingGuardPush (Q := Q) (A := A) (U := U))
      (prepareCouplingGuard (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary) := by
  unfold couplingGuardPush prepareCouplingGuard
  exact embProg_native _ _ _ (WordCmd.empty_native _)

theorem prepareRetainedCouplingPacket_native :
    mnNativePushBound (retainedCouplingPacketPush (Q := Q) (A := A) (U := U))
      (prepareRetainedCouplingPacket (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  unfold retainedCouplingPacketPush prepareRetainedCouplingPacket
  exact embProg_native _ _ _ (WordCmd.empty_native _)

def runSpatialCouplingRowsWorkspace (K P q w s t u band a b : ℕ) : ℕ :=
  couplingGuardPush (Q := Q) (A := A) (U := U)*prepareCouplingGuardCost s t band a b +
    (retainedCouplingPacketPush (Q := Q) (A := A) (U := U)*
      buildMarkedRowCoefficientPacketCost P q w s t u band 0 +
     runPreparedPacketCouplingRowsWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) K P q w s t u band)

theorem runSpatialCouplingRows_exec_within (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt) (hlen : rhs.length = s)
    (tail rhsTail raw : List (Fin (A+4))) (K : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ K)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hsource : S.R 141 = cstream A w (cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band)++tail)
    (hindex : S.R 107 = []) (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (h143 : S.R 143 = []) (h135 : S.R 135 = [])
    (hxs : ∀ j < s, ∀ x ∈ couplingInputWords boundary t band a b j C, Fits w x)
    (has : ∀ j < s, ∀ z ∈ couplingCoefficientWords P q s t u band j, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ runSpatialCouplingGuardedCost boundary P q w s t u band a b ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        runSpatialCouplingRowsWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) K P q w s t u band a b) 0
        (runSpatialCouplingRows hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail)
          113 (cstream A w (guardedCouplingRowWords P q t u band a b boundary C 0 rhs)++S.R 113))}) := by
  let V := liftedCoefficientWidth P q w s t u band
  obtain ⟨vG,mG,huG,hmG,heG⟩ := prepareCouplingGuard_exec (body := body) boundary hst haS hbS (by omega) raw v S hready
  let G : Stacks 144 A := {S with R := Function.update S.R 136 (couplingGuardSymbols boundary A s t band a b++S.R 136)}
  have hreadyG : CouplingReady P q w s t u band a b raw (embStk groupReg G) := by
    rw [show embStk groupReg G = embStk groupReg S from groupProject_updateR S 136 _ (by decide)]
    exact hready
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := prepareRetainedCouplingPacket_exec (body := body)
    (i := 0) hP (NeZero.pos s) raw vG G hreadyG (by simpa [G] using congrArg List.length hindex)
  let S₁ : Stacks 144 A := {G with R := (Function.update G.R 135
    (markedRowCoefficientPacket A V P q s t u band 0++S.R 135))}
  have hready₁ : CouplingReady P q w s t u band a b raw (embStk groupReg S₁) := by
    rw [show embStk groupReg S₁ = embStk groupReg G from groupProject_updateR G 135 _ (by decide)]
    exact hreadyG
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := runPreparedPacketCouplingRows_exec_within (body := body)
    hQ boundary hA hw5 hqw hst hbS hP C rhs hlen tail (S.R 135) (S.R 136) rhsTail raw K hpush v₁ S₁ hready₁
    (by simpa [S₁,G] using hsource) (by simp [S₁,G]) (by simpa [S₁,G] using hindex) (by simpa [S₁,G] using hrhs)
    (by simpa [S₁,G] using h143) (by simp [S₁,V]) hxs has
  let S₂ : Stacks 144 A := {S₁ with R := (Function.update (Function.update (Function.update (Function.update S₁.R 136 (S.R 136)) 135
    (markedRowCoefficientPacket A V P q s t u band s++S.R 135)) 93 rhsTail)
    113 (cstream A w (guardedCouplingRowWords P q t u band a b boundary C 0 rhs)++S₁.R 113))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 135 v₂ S₂
  have hlen₂ : (S₂.R 135).length = 12*V+1 := by simp [S₂,h135]
  have htG := mn_native_exec_within heG _ (prepareCouplingGuard_native boundary) 0 _
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hmG) _)
  have ht₁ := mn_native_exec_within he₁ _ prepareRetainedCouplingPacket_native 0 _
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hm₁) _)
  have ht₃ := mn_native_exec_within he₃ 0 (by
    simp [uclear,drainR,popDo,keepIn,whileR,peekR,mnNativePushBound,mnActPush])
    0 (mnSize (mk v₂ S₂)+0+0) (by omega)
  have ht := mn_seq_within_add htG (mn_seq_within_add ht₁ (mn_seq_within_add he₂ ht₃))
  refine ⟨v₃,mG+(m₁+(m₂+(24*V+4))),hu₃.trans (hu₂.trans (hu₁.trans huG)),?_,
    (ht.mono (by intro d z hz; dsimp only [runSpatialCouplingRowsWorkspace]; omega)).cast ?_ ?_⟩
  · dsimp only [runSpatialCouplingGuardedCost]; omega
  · rw [hlen₂]; omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h136 : k = 136 <;> by_cases h135' : k = 135 <;> by_cases h113 : k = 113 <;> by_cases h93 : k = 93 <;>
      simp_all [S₂,S₁,G]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
