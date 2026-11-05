module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPublicationTranspose
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreWidthCharge

/-! Publication reuses the polynomial-core routing estimate from gathering.
Counter fit follows from the packet width, rather than an execution oracle. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellMatrix
open FixedStreamedBank

theorem selectedPolynomialPublicationCosts_le {Q : ℕ}
    (hstates : FixedStreamedBank.stateCount ≤ Q) (cV C e : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (width radius H b W V : ℕ)
      (windows : PublicationWindows (Sizes.s n i) (H-2*radius)),
      0 < width → width ≤ C*(Sizes.p n)^e → radius ≤ width →
      H ∈ coreGatherLengths (Sizes.s n i) width radius →
      windows.origins.length = (coreGatherIndices (Sizes.s n i) width radius H).length →
      (Sizes.p n)^2 ≤ H-2*radius → H-2*radius ≤ Sizes.s n i → 1 ≤ W →
      V ≤ cV*Sizes.p n → 2^b ≤ Sizes.T n →
      let a := Nat.clog 2 windows.origins.length
      (1700*(2^b*(Sizes.s n i*W) : ℕ)+100*V+500+Sizes.T n+
          2*restoringTimeCost hstates a b ((H-2*radius)*W) V : ℝ) ≤
        2*Sizes.T n+1700*(2^b*(Sizes.s n i*W) : ℕ)+
          108*(generatedDyadicStageCoeff tapeCount 6 1+300)*
            (2^b*(Sizes.s n i*W) : ℕ)*Sizes.d n*((Sizes.ℓ n : ℝ)^Parameters.tau+1) ∧
      3200*(2^b*(Sizes.s n i*W))+200*V+800+Sizes.T n+
          restoringStockAllowance hstates a b ((H-2*radius)*W) V ≤
        2*Sizes.T n+(3200+3*(streamedDyadicStockCoeff tapeCount+40))*(2^b*(Sizes.s n i*W)) := by
  filter_upwards [selectedPublicationTransposeCosts_le hstates cV,
    selectedPublicationCounterFits cV,selectedPolynomialCoreRouteCharge_le C e] with n hbill hfit hroute
  intro h i width radius H b W V windows hw hpoly hr hgroup hcount hprepare hspan hW hV hvolume
  dsimp only
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hpacket : 0 < (H-2*radius)*W := Nat.mul_pos (by nlinarith only [hp,hprepare]) hW
  obtain ⟨ht,hs⟩ := hbill h i (H-2*radius) b W V windows hspan hpacket hV (hfit _ _ _ _ _ hV hprepare hW)
  have hcharge := hroute h i b width radius H (selectedReplicaExponent_le h b hvolume) hw hpoly hr hgroup
  rw [← hcount] at hcharge
  have hcoeff : 0 ≤ 6*(generatedDyadicStageCoeff tapeCount 6 1+300)*(2^b*(Sizes.s n i*W) : ℕ) := by
    have hc : 0 ≤ generatedDyadicStageCoeff tapeCount 6 1+300 := by
      unfold generatedDyadicStageCoeff
      exact add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) Node.swapConst_pos.le)
        (Nat.cast_nonneg _)) (by norm_num)
    exact mul_nonneg (mul_nonneg (by norm_num) hc) (Nat.cast_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hcharge hcoeff
  exact ⟨by nlinarith only [ht,hm],hs⟩

end IntegerMultBounds.MathlibTM2.Cost
