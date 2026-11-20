module

public import IntegerMultBounds.Networks.Certificates.PR589.Nine.Stage
public import IntegerMultBounds.MathlibTM2.Cover.LabelPass

/-! Scalar instructions of the three triangular PR589 stage factors. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Networks IntegerMultBounds.Networks.Certificates.PR589.Nine
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Cover
open Matrix Shared50AffineCoefficients

private theorem two_le_bound : 2 ≤ coefficientBound := by
  simpa only [pow_one] using two_pow_le_coefficientBound
    (show 1 ≤ coefficientExponent by rw [coefficientExponent_eq]; exact Nat.one_le_two_pow)

private theorem half_occurs {z : ℤ} (lo : -2 ≤ z) (hi : z ≤ 2) : Occurs ((z : ℚ)/2) := by
  apply Or.inr
  constructor <;> apply le_trans _ two_le_bound <;> interval_cases z <;> decide +kernel

private theorem sign_scale {q : ℚ} (h : q = 1 ∨ q = -1) : ScaleOccurs q := by
  apply Or.inr
  rcases h with rfl | rfl <;> refine ⟨by decide, le_trans ?_ two_le_bound, le_trans ?_ two_le_bound⟩ <;> decide

/-- The same scalar certificates apply in either column order. In particular
the two upper factors can be compiled after reversing the axis numbering. -/
theorem stageFactor_supported (c : PortCertificate) (checked : c.Checked) (s : Fin 8)
    (e : Fin 64 ≃ Axis) :
    let A := c.spread s
    let ok := fun E : Matrix Axis Axis ℚ => ∀ op ∈ LabelAddress.pass (E.submatrix e e),
      FlatCoordinateSchedule.Supported op
    ok (fromBlocks 1 (-A) 0 1) ∧ ok (fromBlocks 1 0 Aᵀ 1) ∧
      ok (fromBlocks 1 A 0 (avoid s - block s)) := by
  intro A ok
  have one := sign_scale (q := 1) (Or.inl rfl)
  have neg := sign_scale (q := -1) (Or.inr rfl)
  have posShift := scale_occurs one
  have negShift := scale_occurs neg
  have zero : Occurs 0 := by simpa using half_occurs (z := 0) (by decide) (by decide)
  have entry (i x) : Occurs (A i x) ∧ Occurs (-A i x) := by
    obtain ⟨z,lo,hi,h⟩ := c.spread_entry checked s i x
    change Occurs (c.spread s i x) ∧ Occurs (-c.spread s i x)
    rw [h]
    exact ⟨half_occurs lo hi, by simpa only [Int.cast_neg,neg_div] using half_occurs (z := -z) (by omega) (by omega)⟩
  have passes (E : Matrix Axis Axis ℚ) (diag : ∀ i, ScaleOccurs (E i i))
      (off : ∀ i j, Occurs (E i j)) : ok E :=
    LabelPass.supported _ (fun i => diag _) (fun i j _ => off _ _)
  refine ⟨passes _ ?_ ?_,passes _ ?_ ?_,passes _ ?_ ?_⟩
  all_goals intros i; cases i
  all_goals first | (intro j; cases j) | skip
  all_goals simp only [fromBlocks_apply₁₁,fromBlocks_apply₁₂,fromBlocks_apply₂₁,fromBlocks_apply₂₂,
    one_apply,Matrix.zero_apply,Matrix.neg_apply,transpose_apply,Matrix.sub_apply,avoid,block,diagonal_apply]
  all_goals first | exact (entry _ _).1 | exact (entry _ _).2 | exact zero |
    (split_ifs <;> first | exact one | exact zero | contradiction |
      (norm_num only [sub_self,sub_zero,zero_sub]; assumption))
end IntegerMultBounds.MathlibTM2.M6.BitNode
