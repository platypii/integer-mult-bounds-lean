module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGeometryGatherSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeometryGatherSourceBudget

/-! Selected setup is paid by global volume; complete geometry-driven routing
has only source-linear traffic and the sharp dyadic charge left. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix
open PackedTranspose
variable {Q : ℕ}

theorem selectedGeometryGatherCosts_le (hstates : FixedStreamedBank.stateCount ≤ Q) (cV : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (V a width radius L w : ℕ),
    0 < width → width ≤ Sizes.s n i → radius ≤ width → V ≤ cV*Sizes.p n →
    0 < (coreGatherIndices (Sizes.s n i) width radius L).length → 0 < L*w →
    V ≤ 2^a*2^Nat.clog 2 (coreGatherIndices (Sizes.s n i) width radius L).length*(L*w) →
    let b := Nat.clog 2 (coreGatherIndices (Sizes.s n i) width radius L).length
    (geometryGatherTimeCost hstates V (Sizes.s n i) a width radius L w : ℝ) ≤
      Sizes.T n+6000*(2^a*Sizes.s n i*w : ℕ)+
        24*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (2^a*Sizes.s n i*w : ℕ)*dyadicRouteCharge a b ∧
    geometryGatherStockAllowance hstates V (Sizes.s n i) a width radius L w ≤
      Sizes.T n+12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700)*(2^a*Sizes.s n i*w) := by
  filter_upwards [selectedGeometryGatherSetup_le cV] with n hsetup
  intro h i V a width radius L w hw hwidth hradius hV hcores hpacket hfit
  dsimp only
  obtain ⟨htSetup,hsSetup⟩ := hsetup h i V width radius L hw hV
  have ht := geometryGatherTimeCost_le_source hstates V (Sizes.s n i) a width radius L w hwidth hradius hcores hpacket hfit
  have hs := geometryGatherStockAllowance_le_source hstates V (Sizes.s n i) a width radius L w hwidth hradius hcores hpacket hfit
  constructor
  · have htSetupR := (Nat.cast_le (α := ℝ)).mpr htSetup
    push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at ht htSetupR ⊢
    linarith only [ht,htSetupR]
  · have hs' := Nat.add_le_add_right hsSetup
      (12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700)*(2^a*Sizes.s n i*w))
    exact hs.trans (by simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hs')

end IntegerMultBounds.MathlibTM2.Cost
