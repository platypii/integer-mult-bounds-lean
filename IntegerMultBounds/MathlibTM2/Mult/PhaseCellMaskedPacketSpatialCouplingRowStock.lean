module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellZeroPacketSpatialCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketSpatialCouplingRowStock

/-! Both guarded packet-row branches retain a common workspace bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

@[irreducible] def zeroPacketSpatialCouplingRowPush : ℕ :=
  mnProgPush (zeroPacketSpatialCouplingRow (P₀ := P₀) (Q := Q) (A := A) (U := U))

theorem zeroPacketSpatialCouplingRow_native :
    mnNativePushBound (zeroPacketSpatialCouplingRowPush (P₀ := P₀) (Q := Q) (A := A) (U := U))
      (zeroPacketSpatialCouplingRow (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  unfold zeroPacketSpatialCouplingRowPush
  apply WordCmd.native_of_noCalls _ le_rfl
  simp [zeroPacketSpatialCouplingRow, advanceMarkedBinaryPacket, takeMarkedWidth,
    advanceBinaryPacket, takePrefix, transfer, countIter, publishMarkedWidth,
    copyPrefix, copyR, incrField, ucopy, umulSym, scanR, drainR, moveR, whileR, uclear, WordCmd.NoCalls]

def guardedPacketSpatialCouplingRowWorkspace (K P q w s t u band : ℕ) : ℕ :=
  zeroPacketSpatialCouplingRowPush (P₀ := P₀) (Q := Q) (A := A) (U := U)*
    zeroPacketSpatialCouplingRowCost P q w s t u band +
    packetSpatialCouplingRowWorkspace (Q := Q) (A := A) (U := U) K P q w s t u band

theorem guardedPacketSpatialCouplingRow_exec_within (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary skip : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (tail packetTail raw : List (Fin (A+4)))
    (K : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ K)
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
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        guardedPacketSpatialCouplingRowWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) K P q w s t u band) 0
        (guardedPacketSpatialCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 113
          (csyms A w (guardedCouplingRowWord P q t u band a b i boundary C rhs)++S.R 113)) 135
          (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++packetTail))}) := by
  cases skip with
  | true =>
    obtain ⟨v',hu,he⟩ := zeroPacketSpatialCouplingRow_exec (body := body) raw packetTail rhsTail rhs v S hready hpacket hrhs
    refine ⟨v',zeroPacketSpatialCouplingRowCost P q w s t u band+1,hu,by simp,?_⟩
    simp only [guardedCouplingRowWord,← hskip,ite_true]
    have ht := mn_native_exec_within he _ zeroPacketSpatialCouplingRow_native 0 _ (Nat.le_refl _)
    exact .cond_true hflag (ht.mono (by
      intro d z hz
      dsimp only [guardedPacketSpatialCouplingRowWorkspace]
      omega))
  | false =>
    obtain ⟨v',m,hu,hm,he⟩ := packetSpatialCouplingRow_exec_within (body := body)
      hQ boundary hA hw5 hqw hst hi hP C tail packetTail raw K hpush v S hready hpacket hsrc rhs rhsTail hrhs hxs has
    exact ⟨v',m+1,hu,by simpa using Nat.add_le_add_right hm 1,by
      simp only [guardedCouplingRowWord,← hskip,Bool.false_eq_true,ite_false]
      exact .cond_false hflag (he.mono (by
        intro d z hz
        dsimp only [guardedPacketSpatialCouplingRowWorkspace]
        omega))⟩

theorem maskedPacketSpatialCouplingRow_exec_within (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary skip : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (tail packetTail raw : List (Fin (A+4)))
    (maskTail : List (Fin (A+4))) (K : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ K)
    (v : HS 144 Q A U) (S : Stacks 144 A)
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
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        guardedPacketSpatialCouplingRowWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) K P q w s t u band) 0
        (maskedPacketSpatialCouplingRow hQ) (mk v S) m
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
  obtain ⟨v',m,hu,hm,he⟩ := guardedPacketSpatialCouplingRow_exec_within (body := body)
    hQ boundary skip hA hw5 hqw hst hi hP C tail packetTail raw K hpush v₀ S₀ rfl hskip hready₀
    (by simpa [S₀] using hpacket) (by simpa [S₀] using hsrc) rhs rhsTail
    (by simpa [S₀] using hrhs) hxs has
  have ht₀ := mn_native_exec_within he₀ 0 (by change 0 ≤ 0; exact le_refl _) 0 (mnSize (mk v S)+0+0) (by omega)
  have ht := mn_seq_within_add ht₀ he
  refine ⟨v',1+m,hu,by omega,(ht.mono (by intro d z hz; omega)).cast rfl ?_⟩
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
