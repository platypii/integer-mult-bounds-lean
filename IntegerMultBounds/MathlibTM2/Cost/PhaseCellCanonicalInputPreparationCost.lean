module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSharedBoundaryPreparation
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedHaloCommonWidth

/-! Canonical RHS preparation pays shared scalar work once and linear payload
traffic. The arbitrary borrowed suffix never enters these bounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {s : ℕ} [NeZero s]

theorem canonicalInputCopyCost_le (p u l target t N : ℕ) :
    let W := packedHaloCommonWidth p l s u (target+1) 2
    canonicalInputCopyCost p u l target s t N ≤ 60*N*s*W+12*W+44 := by
  let W := packedHaloCommonWidth p l s u (target+1) 2
  have hw := inverseFullInputWidth_le_common (s := s) p u l target t
  have hm := inverseFullInputWidth_eq_master (s := s) p u l target t
  have hW : 1 ≤ W := by
    dsimp only [W,packedHaloCommonWidth,executionWidth,executionPrecision]
    omega
  have hc := generatedCopyNarrowPrefixCost_le N s W (inverseFullInputWidth p u l target s t)
    (NeZero.one_le) hW hw
  dsimp only [canonicalInputCopyCost, W] at *
  omega

theorem canonicalInputPreparationTime_le (p u l target t N : ℕ) :
    let B := inverseCallerWordWidth p u l target s t
    let W := packedHaloCommonWidth p l s u (target+1) 2
    canonicalInputPreparationTime p u l target s t N ≤
      generateInverseMastersCost B p u l target s t 0 s+
        callerInputMasterRetireCost p u l target s t+56*B+60*N*s*W+12*W+103 := by
  have hc := canonicalInputCopyCost_le (s := s) p u l target t N
  dsimp only [canonicalInputPreparationTime, callerCanonicalInputCopyCost]
  omega

theorem canonicalInputPreparationStock_le_time (p u l target t N : ℕ) :
    canonicalInputPreparationStock p u l target s t N ≤
      8*canonicalInputPreparationTime p u l target s t N := by
  unfold canonicalInputPreparationStock canonicalInputPreparationTime generateInverseMastersCost
  dsimp only
  omega

/-- Shared preparation contains only scalar construction and tape movement,
so the same ledger controls temporary stock. -/
theorem sharedBoundaryPreparationStock_le_time (p u l target t D N radius width Vg Vr : ℕ) :
    sharedBoundaryPreparationStock p u l target s t D N radius width Vg Vr ≤
      8*sharedBoundaryPreparationTime p u l target s t D N radius width Vg Vr := by
  have hc := canonicalInputPreparationStock_le_time (s := s) p u l target t N
  dsimp only [sharedBoundaryPreparationStock, sharedBoundaryPreparationTime]
  omega

theorem selectedCanonicalInputCopyCost_le (ct : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (u target N : ℕ)
    (htarget : target ≤ ct*Sizes.p n)
    (hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i) :
    canonicalInputCopyCost (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      target (Sizes.s n i) (Sizes.t n i) N ≤
      (60*(1032+8*ct))*(N*Sizes.s n i*Sizes.p n)+(12*(1032+8*ct)+44)*Sizes.p n := by
  have hc := canonicalInputCopyCost_le (s := Sizes.s n i) (Sizes.p n) u
    (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.t n i) N
  have hw := selectedPackedHaloCommonWidth_le ct h i u target htarget hband
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have htraffic := Nat.mul_le_mul_left (60*N*Sizes.s n i) hw
  have hscalar := Nat.mul_le_mul_left 12 hw
  dsimp only at hc
  nlinarith only [hc,htraffic,hscalar,hp]

end IntegerMultBounds.MathlibTM2.Cost
