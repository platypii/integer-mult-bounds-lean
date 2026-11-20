module

public import IntegerMultBounds.Networks.Certificates.PR589.Nine.Charts
public import IntegerMultBounds.MathlibTM2.Cover.LabelPass

/-! Scalar instructions of the three triangular PR589 stage factors. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Networks IntegerMultBounds.Networks.Certificates.PR589.Nine
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Cover
open Matrix Shared50AffineCoefficients IntegerMultBounds.Swap.Modular
open Shared50ModularControl (prime prime_prime)

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
    (e : Fin 64 ≃ Axis) (w : ℕ) :
    let A := c.spread s
    let ok := fun E : Matrix Axis Axis ℚ => Admissible (prime^w) E ∧
      ∀ op ∈ LabelAddress.pass (E.submatrix e e), FlatCoordinateSchedule.Supported op
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
    ⟨fun i j => Nat.Coprime.pow_right w ((Nat.coprime_of_lt_prime (E i j).den_pos.ne'
      (denominator_bound (off i j)) prime_prime).symm), LabelPass.supported _ (fun i => diag _) (fun i j _ => off _ _)⟩
  refine ⟨passes _ ?_ ?_,passes _ ?_ ?_,passes _ ?_ ?_⟩
  all_goals intros i; cases i
  all_goals first | (intro j; cases j) | skip
  all_goals simp only [fromBlocks_apply₁₁,fromBlocks_apply₁₂,fromBlocks_apply₂₁,fromBlocks_apply₂₂,
    one_apply,Matrix.zero_apply,Matrix.neg_apply,transpose_apply,Matrix.sub_apply,avoid,block,diagonal_apply]
  all_goals first | exact (entry _ _).1 | exact (entry _ _).2 | exact zero |
    (split_ifs <;> first | exact one | exact zero | contradiction |
      (norm_num only [sub_self,sub_zero,zero_sub]; assumption))

/-- The physical numbering places the eight local axes before the eight
exterior blocks. -/
def stageAxis : Axis ≃ Fin 64 :=
  (Equiv.sumCongr (Equiv.refl (Fin 8)) finProdFinEquiv).trans finSumFinEquiv

theorem stageFactor_order (c : PortCertificate) (s : Fin 8) :
    let A := c.spread s
    let upper := fun E : Matrix Axis Axis ℚ => ∀ i j, stageAxis j < stageAxis i → E i j = 0
    let lower := fun E : Matrix Axis Axis ℚ => ∀ i j, stageAxis i < stageAxis j → E i j = 0
    upper (fromBlocks 1 (-A) 0 1) ∧ lower (fromBlocks 1 0 Aᵀ 1) ∧
      upper (fromBlocks 1 A 0 (avoid s - block s)) := by
  intro A upper lower
  have sep (i : Fin 8) (x : Exterior) : stageAxis (.inl i) < stageAxis (.inr x) := by
    change i.val < 8 + (finProdFinEquiv x).val
    omega
  refine ⟨?_,?_,?_⟩
  all_goals rintro (i | x) (j | y) lt
  all_goals first
    | rfl
    | exact False.elim ((not_lt_of_ge (sep _ _).le) lt)
    | (have ne := ne_of_lt lt
       simp only [ne_eq,EmbeddingLike.apply_eq_iff_eq,Sum.inl.injEq,Sum.inr.injEq] at ne
       simp [one_apply,avoid,block,ne,Ne.symm ne])

/-- The modular product is the certified stage involution. Each pass is
invertible in any numbering of the axes, including the reversed numbering. -/
theorem stageFactor_reduce (c : PortCertificate) (checked : c.Checked) (s : Fin 8)
    (e : Fin 64 ≃ Axis) (w : ℕ) :
    let A := c.spread s
    let L := fromBlocks 1 (-A) 0 1
    let M := fromBlocks 1 0 Aᵀ 1
    let R := fromBlocks 1 A 0 (avoid s - block s)
    let unit := fun E : Matrix Axis Axis ℚ => IsUnit (reduce (prime^w) (E.submatrix e e))
    reduce (prime^w) (c.route s) = reduce (prime^w) L * (reduce (prime^w) M * reduce (prime^w) R) ∧
      unit L ∧ unit M ∧ unit R ∧ reduce (prime^w) (c.route s) * reduce (prime^w) (c.route s) = 1 := by
  intro A L M R unit
  obtain ⟨⟨hl,_⟩,⟨hm,_⟩,hr,_⟩ := stageFactor_supported c checked s e w
  have product : c.route s = L*(M*R) := c.route_triangular_factors checked s
  have adm := admissible_mul (prime^w) hl (admissible_mul (prime^w) hm hr)
  have routeAdm : Admissible (prime^w) (c.route s) := product ▸ adm
  have reduced : reduce (prime^w) (c.route s) = reduce (prime^w) L * (reduce (prime^w) M * reduce (prime^w) R) := by
    rw [product,reduce_mul (prime^w) hl (admissible_mul (prime^w) hm hr),reduce_mul (prime^w) hm hr]
  refine ⟨reduced,?_⟩
  have inv := reduce_inverse (prime^w) routeAdm routeAdm (c.route_mul_self checked s)
  have invertible := isUnit_iff_exists.mpr ⟨_,inv,inv⟩
  have determinant := (isUnit_iff_isUnit_det _).mp invertible
  rw [reduced,det_mul,det_mul,(Commute.all _ _).isUnit_mul_iff,(Commute.all _ _).isUnit_mul_iff] at determinant
  have renumber (E : Matrix Axis Axis ℚ) (h : IsUnit (reduce (prime^w) E).det) : unit E := by
    apply (isUnit_iff_isUnit_det _).mpr
    change IsUnit (((reduce (prime^w) E).submatrix e e).det)
    rwa [det_submatrix_equiv_self]
  exact ⟨renumber L determinant.1,renumber M determinant.2.1,renumber R determinant.2.2,inv⟩
/-- A helper chart consists of the half-line, the seven complement columns,
and exterior coordinate columns, permuted into the slot order. -/
theorem helperChart_entry (c : PortCertificate) (checked : c.Checked) (x : ℕ) (hx : x ≤ 55)
    (a b : Axis) :
    (c.helperChart x hx a b).num.natAbs ≤ 2 ∧ (c.helperChart x hx a b).den ≤ 2 := by
  let small := fun q : ℚ => q.num.natAbs ≤ 2 ∧ q.den ≤ 2
  have half {z : ℤ} (lo : -2 ≤ z) (hi : z ≤ 2) : small ((z : ℚ)/2) := by
    interval_cases z <;> decide +kernel
  change small (c.fullChart a (slotPerm x hx b))
  generalize slotPerm x hx b = k
  have zero : small 0 := by decide
  have one : small 1 := by decide
  rcases k with l | (k | y) <;> rcases a with i | z
  · change small ((c.line i : ℚ)/2)
    have sq := Finset.single_le_sum (f := fun j => c.line j * c.line j)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
    rw [checked.1] at sq
    apply half <;> nlinarith
  · exact zero
  · obtain ⟨n,lo,hi,eq⟩ := c.spread_entry checked 0 i (0,k)
    change small (c.complement i k)
    simp only [PortCertificate.spread,Matrix.of_apply,ite_true,eq_self] at eq
    rw [eq]
    exact half lo hi
  · exact zero
  · exact zero
  · change small ((1 : Matrix Exterior Exterior ℚ) z y)
    rw [one_apply]
    split <;> assumption

-- The explicit slot permutation and eight-axis basis decomposition are in 34789f13.

/-- Over every prime-power width the helper chart's transpose undoes the
chart in either order, and its eight local columns are the selected slot. -/
theorem helperChart_reduce (c : PortCertificate) (checked : c.Checked) (x : ℕ) (hx : x ≤ 55)
    (w : ℕ) :
    let H := reduce (prime^w) (c.helperChart x hx)
    H.transpose * H = 1 ∧ H * H.transpose = 1 ∧
      H * reduce (prime^w) PortCertificate.localChart = reduce (prime^w) (c.slotChart x) := by
  intro H
  have adm : Admissible (prime^w) (c.helperChart x hx) := fun i j =>
    Nat.Coprime.pow_right w ((Nat.coprime_of_lt_prime (c.helperChart x hx i j).den_pos.ne' ((helperChart_entry c checked x hx i j).2.trans_lt Shared50ModularControl.prime_odd) prime_prime).symm)
  have inv := reduce_inverse (prime^w) (fun i j => adm j i) adm (c.helperChart_orthonormal checked x hx)
  change H.transpose * H = 1 at inv
  refine ⟨inv,mul_eq_one_comm.mp inv,?_⟩
  rw [← c.helperChart_local x hx]
  apply (reduce_mul _ adm _).symm
  intro i j
  cases i <;> simp [PortCertificate.localChart]
  split <;> simp
end IntegerMultBounds.MathlibTM2.M6.BitNode
