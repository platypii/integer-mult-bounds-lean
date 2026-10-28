module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedBatchStepTrace

/-! The sum of one scratch allowance per admissible complete key fits in one box volume. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def selectedFamilyKeyStepCost (n : ℕ) (i : Fin (Sizes.d n))
    [NeZero (Sizes.s n i)] (ct A : ℕ) (key : SelectedFamilyKey n i ct) : ℕ :=
  if PhaseCellBand.width (Sizes.p n) key.1 ≤ Sizes.s n i then
    familyComplexBatchStepCost A (Sizes.p n) key.1
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      (Sizes.s n i) (Sizes.t n i) key.2.2.1 key.2.2.2 key.2.1
  else 0

theorem selectedFamilyAllKeysStep_scaled_volume_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ A : ℕ,
      scale*(∑ key : SelectedFamilyKey n i ct, selectedFamilyKeyStepCost n i ct A key) ≤ Sizes.T n := by
  obtain ⟨C,hcost⟩ := selectedFamilyBatchStepCost_poly_le ct
  filter_upwards [hcost,selectedAxisPolynomial_le_volume (scale*2*(ct+1)*C) 4 5] with n hc hv
  intro h i _ A
  have hkey (key : SelectedFamilyKey n i ct) : selectedFamilyKeyStepCost n i ct A key ≤ C*Sizes.t n i^3*Sizes.p n^2 := by
    unfold selectedFamilyKeyStepCost
    split_ifs with hband
    · exact hc h i A key.1 key.2.1 key.2.2.1 key.2.2.2 (by omega) (by omega) hband (by omega) (by omega)
    · exact Nat.zero_le _
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun key _ => hkey key)
  have hcard := selectedFamilyKey_card_le n h i ct
  have hpoly : (∑ key : SelectedFamilyKey n i ct, selectedFamilyKeyStepCost n i ct A key) ≤
      (2*(ct+1)*C)*Sizes.t n i^5*Sizes.p n^4 := by
    calc
      _ ≤ Fintype.card (SelectedFamilyKey n i ct)*(C*Sizes.t n i^3*Sizes.p n^2) := by
        simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul] using hsum
      _ ≤ (2*(ct+1)*Sizes.t n i^2*Sizes.p n^2)*(C*Sizes.t n i^3*Sizes.p n^2) :=
        Nat.mul_le_mul_right _ hcard
      _ = (2*(ct+1)*C)*Sizes.t n i^5*Sizes.p n^4 := by ring
  exact (Nat.mul_le_mul_left scale hpoly).trans
    ((by convert hv i using 1 <;> ring) : scale*((2*(ct+1)*C)*Sizes.t n i^5*Sizes.p n^4) ≤ Sizes.T n)

end IntegerMultBounds.MathlibTM2.Cost
