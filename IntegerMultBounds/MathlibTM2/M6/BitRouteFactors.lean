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
theorem stageFactor_supported_rows (k : ℕ) (c : PortCertificate) (checked : c.Checked) (s : Fin 8)
    (e : Fin 64 ≃ Axis) (w : ℕ) :
    let A := c.spread s
    let ok := fun E : Matrix Axis Axis ℚ => Admissible (prime^w) E ∧
      ∀ op ∈ LabelAddress.rowPass k (E.submatrix e e), FlatCoordinateSchedule.Supported op
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
      (denominator_bound (off i j)) prime_prime).symm), LabelPass.supported_rows k _ (fun i => diag _) (fun i j _ => off _ _)⟩
  refine ⟨passes _ ?_ ?_,passes _ ?_ ?_,passes _ ?_ ?_⟩
  all_goals intros i; cases i
  all_goals first | (intro j; cases j) | skip
  all_goals simp only [fromBlocks_apply₁₁,fromBlocks_apply₁₂,fromBlocks_apply₂₁,fromBlocks_apply₂₂,
    one_apply,Matrix.zero_apply,Matrix.neg_apply,transpose_apply,Matrix.sub_apply,avoid,block,diagonal_apply]
  all_goals first | exact (entry _ _).1 | exact (entry _ _).2 | exact zero |
    (split_ifs <;> first | exact one | exact zero | contradiction |
      (norm_num only [sub_self,sub_zero,zero_sub]; assumption))

theorem stageFactor_supported (c : PortCertificate) (checked : c.Checked) (s : Fin 8)
    (e : Fin 64 ≃ Axis) (w : ℕ) :
    let A := c.spread s
    let ok := fun E : Matrix Axis Axis ℚ => Admissible (prime^w) E ∧
      ∀ op ∈ LabelAddress.pass (E.submatrix e e), FlatCoordinateSchedule.Supported op
    ok (fromBlocks 1 (-A) 0 1) ∧ ok (fromBlocks 1 0 Aᵀ 1) ∧
      ok (fromBlocks 1 A 0 (avoid s - block s)) := stageFactor_supported_rows 64 c checked s e w

/-- The physical numbering places the eight local axes before the eight
exterior blocks. -/
def stageAxis : Axis ≃ Fin 64 :=
  (Equiv.sumCongr (Equiv.refl (Fin 8)) finProdFinEquiv).trans finSumFinEquiv

/-- Move just the seven exterior coordinates used by a stage to the front.
The eighth local coordinate stays behind them. -/
def stageColumnNumber (s : Fin 8) (j : Fin 64) : Fin 64 :=
  let start := 8 + 7*s.val
  if h : j.val < 7 then ⟨start+j.val, by have := s.isLt; omega⟩
  else if start ≤ j.val ∧ j.val < start+7 then ⟨j.val-start, by omega⟩ else j

theorem stageColumn_involutive : ∀ (s : Fin 8) (j : Fin 64),
    stageColumnNumber s (stageColumnNumber s j) = j := by decide +kernel

def stageColumns (s : Fin 8) : Equiv.Perm (Fin 64) :=
  ⟨stageColumnNumber s,stageColumnNumber s,stageColumn_involutive s,stageColumn_involutive s⟩

def stageColumnPairs (s : Fin 8) : List {p : Fin 64 × Fin 64 // p.1 < p.2} :=
  List.ofFn fun j : Fin 7 =>
    ⟨(⟨j.val, by omega⟩, ⟨8+7*s.val+j.val, by have := s.isLt; have := j.isLt; omega⟩), by
      change j.val < 8+7*s.val+j.val
      omega⟩

theorem stageColumnPairs_length (s : Fin 8) : (stageColumnPairs s).length = 7 := List.length_ofFn

theorem stageColumnPairs_prod (s : Fin 8) :
    ((stageColumnPairs s).map fun p => Equiv.swap p.val.1 p.val.2).prod = stageColumns s := by
  have entries : ∀ (s : Fin 8) (j : Fin 64),
      ((stageColumnPairs s).map fun p => Equiv.swap p.val.1 p.val.2).prod j = stageColumns s j := by
    decide +kernel
  exact Equiv.ext (entries s)

private theorem stageColumns_before : ∀ (s : Fin 8) (i : Fin 8) (j : Fin 7),
    stageColumns s (stageAxis (.inr (s,j))) < stageColumns s (stageAxis (.inl i)) := by
  decide +kernel

/-- In the seven-swap column order both formerly upper factors are lower. -/
theorem stageFactor_seven_order (c : PortCertificate) (s : Fin 8) :
    let e := (stageColumns s).trans stageAxis.symm
    let A := c.spread s
    let lower := fun E : Matrix Axis Axis ℚ => IntegerMultBounds.Swap.Shear.LowerTriangular (E.submatrix e e)
    lower (fromBlocks 1 (-A) 0 1) ∧ lower (fromBlocks 1 A 0 (avoid s - block s)) := by
  intro e A lower
  have zero (i j : Fin 64) (lt : i < j) : (e i) ≠ (e j) := fun h => lt.ne (e.injective h)
  have above (i j : Fin 64) (lt : i < j) (a : Fin 8) (x : Exterior)
      (hi : e i = .inl a) (hj : e j = .inr x) : A a x = 0 := by
    change (if x.1 = s then _ else _) = 0
    apply if_neg
    rintro eq
    have key := stageColumns_before s a x.2
    have left := congrArg e.symm hi
    have right := congrArg e.symm hj
    simp only [Equiv.symm_apply_apply] at left right
    rw [left,right] at lt
    exact (not_lt_of_gt (by simpa [e,stageColumns,← eq] using key)) lt
  constructor <;> intro i j lt
  all_goals
    have ne := zero i j lt
    change (fromBlocks _ _ _ _) (e i) (e j) = 0
    cases hi : e i with
    | inl a =>
      cases hj : e j with
      | inl b => simpa [hi,hj,Matrix.one_apply] using (show a ≠ b by simpa [hi,hj] using ne)
      | inr x => simp [above i j lt a x hi hj]
    | inr x =>
      cases hj : e j with
      | inl a => rfl
      | inr y =>
        have hxy : x ≠ y := by simpa [hi,hj] using ne
        simp [Matrix.one_apply,avoid,block,hxy]

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

private theorem route_admissible (c : PortCertificate) (checked : c.Checked) (s : Fin 8) (w : ℕ) :
    Admissible (prime^w) (c.route s) := by
  obtain ⟨⟨hl,_⟩,⟨hm,_⟩,hr,_⟩ := stageFactor_supported c checked s stageAxis.symm w
  rw [c.route_triangular_factors checked s]
  exact admissible_mul _ hl (admissible_mul _ hm hr)

theorem stageRoute_admissible (c : PortCertificate) (checked : c.Checked) (n : Fin 9) (w : ℕ) :
    Admissible (prime^w) (c.stageRoute n) := by
  unfold PortCertificate.stageRoute
  split
  · exact admissible_one _
  · exact route_admissible c checked _ w

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
  have routeAdm := route_admissible c checked s w
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
/-- The half-line, complement columns and exterior coordinates have half-integral entries. -/
theorem fullChart_entry (c : PortCertificate) (checked : c.Checked) (a : Axis) (k : ChartAxis) :
    (c.fullChart a k).num.natAbs ≤ 2 ∧ (c.fullChart a k).den ≤ 2 := by
  let small := fun q : ℚ => q.num.natAbs ≤ 2 ∧ q.den ≤ 2
  have half {z : ℤ} (lo : -2 ≤ z) (hi : z ≤ 2) : small ((z : ℚ)/2) := by
    interval_cases z <;> decide +kernel
  change small (c.fullChart a k)
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

theorem helperChart_entry (c : PortCertificate) (checked : c.Checked) (x : ℕ) (hx : x ≤ 55)
    (a b : Axis) :
    (c.helperChart x hx a b).num.natAbs ≤ 2 ∧ (c.helperChart x hx a b).den ≤ 2 :=
  fullChart_entry c checked a (slotPerm x hx b)

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
/-- On a covered data port, changing the label by the stage route carries
the modular window projector to the certificate's lifted parent projector. -/
theorem stageProjector_atLabel (c : PortCertificate) (checked : c.Checked) (n : Fin 9) (w : ℕ)
    (U : Matrix (Fin 8) (Fin 8) ℚ) (legal : Admissible (prime^w) U)
    (g : Matrix Axis Axis (ZMod (prime^w))) :
    let m := prime^w
    let H := reduce m (c.stageRoute n)
    let L : Matrix Exterior Exterior (ZMod m) := diagonal fun i => if i.1.val < n.val then 1 else 0
    g * reduce m (c.stageLift n U) * g⁻¹ =
      (g*H) * fromBlocks (reduce m U) 0 0 L * (g*H)⁻¹ := by
  intro m H L
  have route := stageRoute_admissible c checked n w
  have window : Admissible m (windowProj n U) := by
    rintro (i|i) (j|j)
    · exact legal i j
    · simp [windowProj]
    · simp [windowProj]
    · simp only [windowProj,fromBlocks_apply₂₂,lower,diagonal_apply]
      split_ifs <;> simp
  have red : reduce m (windowProj n U) = fromBlocks (reduce m U) 0 0 L := by
    ext (i|i) (j|j)
    all_goals simp only [reduce,Matrix.map_apply,windowProj,fromBlocks_apply₁₁,fromBlocks_apply₁₂,
      fromBlocks_apply₂₁,fromBlocks_apply₂₂,Matrix.zero_apply,ratMod_zero,L,lower,diagonal_apply]
    split_ifs <;> simp [ratMod_zero,ratMod_one]
  have inv : H⁻¹ = H := Matrix.inv_eq_right_inv (reduce_inverse m route route (c.stageRoute_mul_self checked n))
  rw [c.stageLift_eq,reduce_mul m (admissible_mul m route window) route,reduce_mul m route window,
    red,Matrix.mul_inv_rev,inv]
  simp only [H,Matrix.mul_assoc]

/-- In a helper's modular chart, exchanging the scheduled parent span is
exactly the exchange of the eight local axes. -/
theorem helperChart_span (c : PortCertificate) (checked : c.Checked) (x : ℕ) (hx : x ≤ 55) (w : ℕ) :
    let H := reduce (prime^w) (c.helperChart x hx)
    let S := reduce (prime^w) (c.span x (x+8))
    H.transpose * S = (fromBlocks 1 0 0 (0 : Matrix Exterior Exterior (ZMod (prime^w)))) * H.transpose := by
  intro H S
  let J : Matrix Axis Axis ℚ := fromBlocks 1 0 0 (0 : Matrix Exterior Exterior ℚ)
  have adm : Admissible (prime^w) (c.helperChart x hx) := fun i j =>
    Nat.Coprime.pow_right w ((Nat.coprime_of_lt_prime (c.helperChart x hx i j).den_pos.ne'
      ((helperChart_entry c checked x hx i j).2.trans_lt Shared50ModularControl.prime_odd) prime_prime).symm)
  have legal : Admissible (prime^w) J := by
    intro i j
    cases i <;> cases j <;> simp [J,Matrix.fromBlocks,Matrix.one_apply] <;> split <;> simp
  have red : reduce (prime^w) J = fromBlocks 1 0 0 (0 : Matrix Exterior Exterior (ZMod (prime^w))) := by
    ext i j
    cases i <;> cases j <;> simp [J,reduce,Matrix.fromBlocks,Matrix.one_apply,ratMod_zero] <;>
      split <;> simp [ratMod_one,ratMod_zero]
  have trans : Admissible (prime^w) (c.helperChart x hx).transpose := fun i j => adm j i
  have span : S = H * reduce (prime^w) J * H.transpose := by
    dsimp only [S,H]
    rw [← c.helperChart_slot x hx,reduce_mul _ (admissible_mul _ adm legal) trans,
      reduce_mul _ adm legal]
    rfl
  rw [span,← Matrix.mul_assoc,← Matrix.mul_assoc,(helperChart_reduce c checked x hx w).1,Matrix.one_mul,red]

/-- Axis order of the eight live digits and the 56 exterior digits in a slot. -/
noncomputable def helperSlotOrder (x : ℕ) (hx : x ≤ 55) : Axis ≃ ChartAxis :=
  Equiv.ofBijective (slotPerm x hx) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨slotPerm_injective x hx,by decide⟩)

/-- On the same port, changing helper slots only permutes the 64 digits
of a charted field. The new live digits can come from the old exterior. -/
theorem helperSlot_reindex (c : PortCertificate) (x y : ℕ) (hx : x ≤ 55) (hy : y ≤ 55)
    (w : ℕ) (v : Axis → ZMod (prime^w)) :
    let H := fun z hz => (reduce (prime^w) (c.helperChart z hz)).transpose
    let order := (helperSlotOrder y hy).trans (helperSlotOrder x hx).symm
    H y hy *ᵥ v = (H x hx *ᵥ v) ∘ order := by
  intro H order
  funext i
  have same : slotPerm x hx (order i) = slotPerm y hy i :=
    (helperSlotOrder x hx).apply_symm_apply _
  change (∑ j, _ * v j) = ∑ j, _ * v j
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold H reduce
  simp only [Matrix.transpose_apply,PortCertificate.helperChart,Matrix.of_apply,Matrix.map_apply,same]

end IntegerMultBounds.MathlibTM2.M6.BitNode
