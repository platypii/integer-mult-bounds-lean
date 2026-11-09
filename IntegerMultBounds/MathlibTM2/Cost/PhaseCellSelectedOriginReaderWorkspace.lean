module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadSupplierEndpoints
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Reading a class origin is shared work, charged once before its fitting
batch. The binary format width stays explicit in the selected contract. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedOriginReaderWorkspace_le (cV : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (_h : Sizes.Big m) (i : Fin (Sizes.d m)),
      ∀ V a n : ℕ, V ≤ cV*Sizes.p m → a ≤ Sizes.s m i → n ≤ Sizes.s m i →
      3*readSupplierEndpointsCost V a n ≤ Sizes.T m := by
  filter_upwards [selectedAxisPolynomial_le_volume (57*cV+108) 1 1] with m hv
  intro h i V a n hV ha hn
  have ht : 1 ≤ Sizes.t m i := by have := h.good.lt i; omega
  have hp : 1 ≤ Sizes.p m := by have := h.thirteen_le_p; omega
  have htP := Nat.le_mul_of_pos_right (Sizes.t m i) hp
  have hpT := Nat.le_mul_of_pos_left (Sizes.p m) ht
  have hunit : 1 ≤ Sizes.t m i*Sizes.p m := Nat.mul_pos ht hp
  have hVaxis := hV.trans (Nat.mul_le_mul_left cV hpT)
  have haAxis := ha.trans ((h.good.lt i).le.trans htP)
  have hnAxis := hn.trans ((h.good.lt i).le.trans htP)
  have hvolume := hv i
  simp only [pow_one] at hvolume
  unfold readSupplierEndpointsCost
  nlinarith only [hVaxis,haAxis,hnAxis,hunit,hvolume]

end IntegerMultBounds.MathlibTM2.Cost
