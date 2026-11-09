module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicPagePreparationCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCyclicFactorFromCached

/-! Page preparation is shared setup. Its physical geometry width is already
linear in the axis length, so no extra numerical profile is needed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedCyclicBoundaryPageWorkspace_le :
    ∀ᶠ m : ℕ in atTop, ∀ (_h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
      ∀ (R : Regs 154 A) (band a n : ℕ), band ≤ Sizes.s m i → a ≤ Sizes.s m i → n ≤ Sizes.s m i →
      (R 121).length = Sizes.s m i → (R 141).length = a → (R 142).length = n →
      cyclicFactorPreparationPush (Q := Q) (A := A) (U := U)*
        prepareCyclicBoundaryPageCost R (Sizes.s m i) (Sizes.t m i) band a n ≤ Sizes.T m := by
  let push := cyclicFactorPreparationPush (Q := Q) (A := A) (U := U)
  filter_upwards [selectedAxisPolynomial_le_volume (push*300000*11^3) 0 3] with m hv
  intro h i _ R band a n hb ha hn hsSrc haSrc hnSrc
  let t := Sizes.t m i
  have hst : Sizes.s m i < t := h.good.lt i
  have ht : 1 ≤ t := by have := NeZero.pos (Sizes.s m i); omega
  have hsizeT : Nat.size t ≤ t := Nat.size_le.mpr Nat.lt_two_pow_self
  have hsizeB : Nat.size band ≤ band := Nat.size_le.mpr Nat.lt_two_pow_self
  have hV : publicationGeometryWidth t band ≤ 11*t := by
    unfold publicationGeometryWidth
    omega
  have hpage := prepareCyclicBoundaryPageCost_poly R t band a n (11*t)
    (by omega) (by omega) (by omega) (by omega) ha hn hV hsSrc haSrc hnSrc
  calc
    push*prepareCyclicBoundaryPageCost R (Sizes.s m i) t band a n ≤
        push*(300000*(11*t)^3) := Nat.mul_le_mul_left push hpage
    _ = (push*300000*11^3)*t^3*(Sizes.p m)^0 := by ring
    _ ≤ Sizes.T m := hv i

end IntegerMultBounds.MathlibTM2.Cost
