module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreControl
public import IntegerMultBounds.NLogN.PhaseCellCoreLocalityGeometry

/-! Summed scalar control work over the generated classes is an axis polynomial,
so fixed scales and precision-polynomial reserves fit one whole-box allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierSetupPlan

/-- The two movement classes together contain at most twice an axis's core
count. No replica count or data volume enters their shared scalar charge. -/
theorem selectedCoreControlList_scaled_volume_le (C scale k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)], ∀ A : ℕ,
      ∀ jobs : List (PackedNormalizedJob A (Sizes.s n i)), jobs.length ≤ 2*Sizes.t n i →
      (∀ r ∈ jobs,
        coreControlTimeCost r.Bcore r+42*r.inputSharedStock ≤ C*Sizes.t n i^6 ∧
        coreControlStock r.Bcore r+62*r.inputSharedStock ≤ C*Sizes.t n i^6) →
      scale*Sizes.p n^k*(jobs.map (fun r => max
        (coreControlTimeCost r.Bcore r+42*r.inputSharedStock)
        (coreControlStock r.Bcore r+62*r.inputSharedStock))).sum ≤ Sizes.T n := by
  filter_upwards [selectedAxisPolynomial_le_volume (2*scale*C) k 7] with n hn
  intro i _ A jobs hlength hcost
  have hsum := List.sum_le_length_nsmul (jobs.map (fun r => max
      (coreControlTimeCost r.Bcore r+42*r.inputSharedStock)
      (coreControlStock r.Bcore r+62*r.inputSharedStock))) (C*Sizes.t n i^6) (by
    intro x hx
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
    exact max_le (hcost r hr).1 (hcost r hr).2)
  simp only [List.length_map,smul_eq_mul] at hsum
  calc
    _ ≤ scale*Sizes.p n^k*(jobs.length*(C*Sizes.t n i^6)) := Nat.mul_le_mul_left _ hsum
    _ ≤ scale*Sizes.p n^k*((2*Sizes.t n i)*(C*Sizes.t n i^6)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hlength)
    _ = (2*scale*C)*Sizes.t n i^7*Sizes.p n^k := by ring
    _ ≤ Sizes.T n := hn i

end IntegerMultBounds.MathlibTM2.Cost
