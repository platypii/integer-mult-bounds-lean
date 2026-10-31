module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCommonWidth
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInteriorInitialization

/-! The common supplier packet width remains linear in selected precision. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem selectedPackedHaloCommonWidth_le (ct : ℕ) {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n))
    [NeZero (Sizes.s n i)] (u target : ℕ) (htarget : target ≤ ct*Sizes.p n)
    (hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i) :
    packedHaloCommonWidth (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      (Sizes.s n i) u (target+1) 2 ≤ (1032+8*ct)*Sizes.p n := by
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hl := (haloInverseRingLog_bounds hp (h.good.lt i) (h.quarter_p_le_theta i)).1
  have hbits : Nat.size (2*s+1) ≤ Nat.size t+2 := by
    apply Nat.size_le.mpr
    rw [pow_add]
    norm_num
    have := Nat.lt_size_self t
    have hst : s < t := h.good.lt i
    omega
  have htbits := selectedAxisBits_le n i
  have hell : Sizes.ℓ n ≤ p := selectedAxisLog_le_precision h
  have hgeometry : Nat.size (2*s+1) ≤ 2*p := by
    have := h.thirteen_le_p
    dsimp only [t,p] at *
    omega
  have hNlog : Nat.size s ≤ 2*p := (Nat.size_le_size (by omega : s ≤ 2*s+1)).trans hgeometry
  have hBlog : Nat.size (2*PhaseCellBand.width p u+1) ≤ 2*p :=
    (Nat.size_le_size (by change PhaseCellBand.width p u ≤ s at hband; omega)).trans hgeometry
  have hw := inverseExecutionWidth_le p l target s (PhaseCellBand.width p u) 20 ct 2 2
    hp hl htarget hNlog hBlog
  rw [inverseExecutionExponent_eq p u l target s] at hw
  simpa only [packedHaloCommonWidth,boundaryHaloTarget,Nat.add_sub_cancel,
    executionWidth,show 16*20+8*ct+8*2+8*2+680 = 1032+8*ct by omega] using hw
end IntegerMultBounds.MathlibTM2.Cost
