module

public import IntegerMultBounds.MathlibTM2.Routing.RetainedHaloTensor
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum

/-! Partial halo tensors are priced by their exact product volume. Small total
relative halo width bounds every partial stage by twice the original tensor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.RetainedHaloVolume
open RetainedHaloTensor
open scoped BigOperators
variable {ι : Type} [DecidableEq ι]

theorem prod_one_add_le_inv (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hs : ∑ i ∈ s, x i < 1) : ∏ i ∈ s, (1+x i) ≤ (1-∑ i ∈ s, x i)⁻¹ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hxi := hx i (by simp)
    have hxs : ∀ j ∈ s, 0 ≤ x j := fun j hj => hx j (by simp [hj])
    have hsum := Finset.sum_nonneg hxs
    have hs' : ∑ j ∈ s, x j < 1 := by rw [Finset.sum_insert hi] at hs; linarith
    have ht : 0 < 1-(x i+∑ j ∈ s, x j) := by rw [Finset.sum_insert hi] at hs; linarith
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    calc
      (1+x i)*(∏ j ∈ s, (1+x j)) ≤ (1+x i)*(1-∑ j ∈ s, x j)⁻¹ :=
        mul_le_mul_of_nonneg_left (ih hxs hs') (by linarith)
      _ ≤ (1-(x i+∑ j ∈ s, x j))⁻¹ := by
        rw [←div_eq_mul_inv,inv_eq_one_div]
        apply (div_le_div_iff₀ (by linarith : 0 < 1-∑ j ∈ s, x j) ht).2
        nlinarith only [hxi,hsum,mul_nonneg hxi hsum,sq_nonneg (x i)]

noncomputable def overhead (a : Axis) : ℝ := 2*(a.H : ℝ)/(a.L : ℝ)

theorem overhead_nonneg (a : Axis) : 0 ≤ overhead a :=
  div_nonneg (by positivity) (Nat.cast_nonneg _)

section Volume
variable [Fintype ι]

theorem volume_pos (axis : ι → Axis) (retained : Finset ι) : 0 < volume axis retained := by
  apply Finset.prod_pos
  intro i _
  apply Nat.mul_pos (axis i).N_pos
  have hh := (axis i).L_pos
  unfold localLength
  split_ifs <;> omega

theorem volume_ratio (axis : ι → Axis) (retained : Finset ι) :
    (volume axis retained : ℝ) = (volume axis ∅ : ℝ)*(∏ i ∈ retained, (1+overhead (axis i))) := by
  induction retained using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hL : (0 : ℝ) < (axis i).L := Nat.cast_pos.mpr (axis i).L_pos
    have he : (axis i).L*(1+overhead (axis i)) = (axis i).L+2*(axis i).H := by
      unfold overhead
      field_simp
    have hstep : (volume axis (insert i s) : ℝ) = (volume axis s : ℝ)*(1+overhead (axis i)) := by
      apply mul_right_cancel₀ (ne_of_gt hL)
      have hnat := volume_insert_mul axis s i hi
      have hh : (volume axis (insert i s) : ℝ)*(axis i).L =
          (volume axis s : ℝ)*((axis i).L+2*(axis i).H) := by exact_mod_cast hnat
      rw [hh,←he]
      ring
    rw [hstep,ih,Finset.prod_insert hi]
    ring

theorem volume_lt_two (axis : ι → Axis) (retained : Finset ι)
    (hbudget : ∑ i ∈ retained, overhead (axis i) < (1 : ℝ)/2) :
    volume axis retained < 2*volume axis ∅ := by
  have hs : ∑ i ∈ retained, overhead (axis i) < 1 := by linarith
  have hp := prod_one_add_le_inv retained (fun i => overhead (axis i)) (fun i _ => overhead_nonneg (axis i)) hs
  have hb : (1-∑ i ∈ retained, overhead (axis i))⁻¹ < (2 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ (by linarith : 0 < 1-∑ i ∈ retained, overhead (axis i))).2
    linarith
  have hpos : (0 : ℝ) < volume axis ∅ := Nat.cast_pos.mpr (volume_pos axis ∅)
  have hreal : (volume axis retained : ℝ) < 2*(volume axis ∅ : ℝ) := by
    rw [volume_ratio]
    calc
      _ < (volume axis ∅ : ℝ)*2 := mul_lt_mul_of_pos_left (hp.trans_lt hb) hpos
      _ = _ := by ring
  exact_mod_cast hreal

theorem volume_lt_two_uniform (axis : ι → Axis) (retained : Finset ι) (L H : ℕ)
    (hL : ∀ i, (axis i).L = L) (hH : ∀ i, (axis i).H = H) (hLpos : 0 < L)
    (hsmall : 4*Fintype.card ι*H < L) : volume axis retained < 2*volume axis ∅ := by
  apply volume_lt_two
  have hlen : (0 : ℝ) < L := Nat.cast_pos.mpr hLpos
  have hs : (∑ i ∈ retained, overhead (axis i)) = (retained.card : ℝ)*(2*(H : ℝ)/(L : ℝ)) := by
    simp [overhead,hL,hH]
  rw [hs]
  calc
    _ ≤ (Fintype.card ι : ℝ)*(2*(H : ℝ)/(L : ℝ)) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_univ retained)) (by positivity)
    _ < (1 : ℝ)/2 := by
      rw [←mul_div_assoc]
      apply (div_lt_iff₀ hlen).2
      have hh : (4 : ℝ)*(Fintype.card ι : ℝ)*(H : ℝ) < (L : ℝ) := by exact_mod_cast hsmall
      nlinarith only [hh]

theorem volume_lt_two_of_large_core (axis : ι → Axis) (retained : Finset ι) (L H : ℕ)
    (hL : ∀ i, (axis i).L = L) (hH : ∀ i, (axis i).H = H) (hLpos : 0 < L)
    (hlarge : 64*Fintype.card ι*H ≤ L) : volume axis retained < 2*volume axis ∅ := by
  apply volume_lt_two_uniform axis retained L H hL hH hLpos
  nlinarith only [hlarge,hLpos]

end Volume
end IntegerMultBounds.MathlibTM2.Routing.RetainedHaloVolume
