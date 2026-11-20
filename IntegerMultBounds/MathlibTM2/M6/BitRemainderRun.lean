module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalLabel
public import IntegerMultBounds.MathlibTM2.Cover.ProjectorWitness
public import IntegerMultBounds.MathlibTM2.M6.BitCopyLabel
public import IntegerMultBounds.MathlibTM2.M6.BitCopyChildLayout
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalTotalRun

/-! Physical interchange of the unhosted interval on an idle owner's flag coordinates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitHosting
open BitOccurrences

/-- Physical idle intervals, including empty spans, realize the charged rank list. -/
theorem remainderWidths_perm :
    (remainderIntervals.map fun e => e.2 - e.1).Perm remainders := by
  have widths : ∀ i : Fin 9, (idleRanks 4).getD i.val 0 =
      7 * idleTarget i.val - 7 * idleSource i.val := by decide +kernel
  apply List.Perm.trans _ remainders_perm
  apply List.Perm.of_eq
  simp only [remainderIntervals, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro i hi
  apply List.map_congr_left
  intro k _
  rw [widths ⟨i, List.mem_range.mp hi⟩]
  change 7 * idleTarget i - (7 * idleSource i + 8*k) = (7 * idleTarget i - 7 * idleSource i) - 8*k
  omega

end IntegerMultBounds.MathlibTM2.M6.BitHosting

namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open M8.Machine.ArbitraryWidthOriginalTotalRun (program cost input)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)

open RecursiveInterchangeLayout (Descriptor role)
open CopyChildLayout (spectators changeLayout packActive)
open Cover.Fallback (rankDescriptor)

open IntegerMultBounds.Networks.Certificates.PR589.Nine Matrix

/-- In flag coordinates the parent's rational remainder exchange swaps precisely
the selected positions. The omitted line component stays in the identity term. -/
theorem remainderExchange_flag (c : PortCertificate) (lo hi : ℕ) :
    let F := Matrix.fromBlocks c.flag 0 0 c.flag
    exchange (c.span lo hi) = 1 + F * (exchange (interval lo hi) - 1) * Fᵀ := by
  intro F
  simp only [F, exchange, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
    Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, PortCertificate.span]
  ext (i | i) (j | j) <;>
    simp [Matrix.one_apply, Matrix.sub_apply] <;> abel

/-- Projecting both parent address halves into a checked port flag commutes
with the remainder exchange. -/
theorem remainderExchange_read (c : PortCertificate) (hc : c.Checked) (lo hi : ℕ) :
    let F := Matrix.fromBlocks c.flag 0 0 c.flag
    Fᵀ * exchange (c.span lo hi) = exchange (interval lo hi) * Fᵀ := by
  intro F
  have orth : Fᵀ * F = 1 := by
    simp [F, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      c.flag_orthonormal hc, Matrix.fromBlocks_one]
  rw [remainderExchange_flag, Matrix.mul_add, Matrix.mul_one]
  change Fᵀ + Fᵀ * (F * _ * Fᵀ) = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, orth, Matrix.one_mul, Matrix.sub_mul, Matrix.one_mul]
  abel

/-- Reading an actual parent address through the port flag gives an ordinary
interval swap on its 63 pending coordinates. -/
theorem remainderExchange_digits (c : PortCertificate) (hc : c.Checked) (lo hi : ℕ)
    (x : Axis ⊕ Axis → ℚ) :
    let F := Matrix.fromBlocks c.flag 0 0 c.flag
    let digits := Fᵀ *ᵥ x
    Fᵀ *ᵥ (exchange (c.span lo hi) *ᵥ x) =
      Sum.elim (fun p => if lo ≤ pendingIndex p ∧ pendingIndex p < hi then digits (.inr p)
        else digits (.inl p))
        (fun p => if lo ≤ pendingIndex p ∧ pendingIndex p < hi then digits (.inl p)
        else digits (.inr p)) := by
  intro F digits
  rw [Matrix.mulVec_mulVec, remainderExchange_read c hc, ← Matrix.mulVec_mulVec]
  change exchange (interval lo hi) *ᵥ digits = _
  funext i
  cases i with
  | inl p | inr p =>
    by_cases active : lo ≤ pendingIndex p ∧ pendingIndex p < hi <;>
      simp [exchange, Matrix.fromBlocks_mulVec, Matrix.sub_mulVec, interval,
        Matrix.mulVec_diagonal, active]

/-- The remaining coordinate on each half is the line of the port. Both
line projections retain their values under the parent's remainder exchange. -/
theorem remainderExchange_line (c : PortCertificate) (hc : c.Checked) (lo hi : ℕ) :
    let L := Matrix.fromBlocks c.linePart 0 0 c.linePart
    L * exchange (c.span lo hi) = L := by
  intro L
  have line : c.linePart * c.flag = 0 := by
    simp [PortCertificate.linePart, PortCertificate.flag, Matrix.fromBlocks_multiply,
      c.lineProj_mul_complement hc, Matrix.fromBlocks_zero]
  have disjoint : c.linePart * c.span lo hi = 0 := by
    rw [PortCertificate.span, ← Matrix.mul_assoc, ← Matrix.mul_assoc, line,
      Matrix.zero_mul, Matrix.zero_mul]
  simp [L, exchange, Matrix.fromBlocks_multiply, Matrix.mul_sub, disjoint]

open IntegerMultBounds.Swap.Modular

/-- Projecting the reduced parent exchange onto its full port chart exchanges the
same interval on arbitrary modular digits, at every tape width. -/
theorem remainderExchange_chart (c : PortCertificate) (hc : c.Checked) (lo hi w : ℕ)
    (x : IntegerMultBounds.Swap.Shear.State Axis (ZMod (prime^w))) :
    let F := reduce (prime^w) c.fullChart
    let S := reduce (prime^w) (c.span lo hi)
    let y := M8.Exchange.exchange S x
    ∀ p, ((Fᵀ *ᵥ y.1) p, (Fᵀ *ᵥ y.2) p) =
      if lo < chartIndex p ∧ chartIndex p ≤ hi then ((Fᵀ *ᵥ x.2) p, (Fᵀ *ᵥ x.1) p)
      else ((Fᵀ *ᵥ x.1) p, (Fᵀ *ᵥ x.2) p) := by
  intro F S y p
  let m := prime^w
  have chart : Admissible m c.fullChart := by
    intro i j
    have bound := (fullChart_entry c hc i j).2
    exact Nat.Coprime.pow_right w ((Nat.coprime_of_lt_prime (c.fullChart i j).den_pos.ne'
      (bound.trans_lt Shared50ModularControl.prime_odd) Shared50ModularControl.prime_prime).symm)
  have flag : Admissible m c.flag := fun i j => chart i (.inr j)
  let J := reduce m c.flag
  have chartT : Admissible m c.fullChartᵀ := fun i j => chart j i
  have orth : Fᵀ * F = 1 := by
    change reduce m c.fullChartᵀ * reduce m c.fullChart = 1
    rw [← reduce_mul m chartT chart, c.fullChart_orthonormal hc, reduce_one]
  let D : Matrix Pending Pending (ZMod m) := diagonal fun j =>
    if lo ≤ pendingIndex j ∧ pendingIndex j < hi then 1 else 0
  have sel : Admissible m (interval lo hi) := by
    intro i j
    simp only [interval, diagonal_apply]
    split_ifs <;> simp
  have reduced : reduce m (interval lo hi) = D := by
    ext i j
    simp only [reduce, Matrix.map_apply, interval, D, diagonal_apply]
    split_ifs <;> simp [ratMod_zero,ratMod_one]
  have transposed : Admissible m c.flagᵀ := fun i j => flag j i
  have span : S = J * D * Jᵀ := by
    change reduce m (c.flag * interval lo hi * c.flagᵀ) = _
    rw [reduce_mul m (admissible_mul m flag sel) transposed,
      reduce_mul m flag sel, reduced]
    rfl
  have read (v : Axis → ZMod m) :
      (Fᵀ *ᵥ (S *ᵥ v)) p = if lo < chartIndex p ∧ chartIndex p ≤ hi
        then (Fᵀ *ᵥ v) p else 0 := by
    have cols (i j) : (Fᵀ * J) i j = (1 : Matrix ChartAxis ChartAxis (ZMod m)) i (.inr j) :=
      congrFun (congrFun orth i) (.inr j)
    rw [span, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ Fᵀ]
    cases p with
    | inl k => simp [Matrix.mulVec, dotProduct, cols, Matrix.one_apply,chartIndex]
    | inr j =>
      simp only [Matrix.mulVec, dotProduct, cols, Matrix.one_apply, Sum.inr.injEq,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      change (D *ᵥ (Jᵀ *ᵥ v)) j = _
      rw [Matrix.mulVec_diagonal]
      by_cases active : lo ≤ pendingIndex j ∧ pendingIndex j < hi
      · have h : lo < chartIndex (.inr j) ∧ chartIndex (.inr j) ≤ hi := by simp [chartIndex]; omega
        simp only [D,active,h,and_self,if_true,one_mul]
        rfl
      · have h : ¬(lo < chartIndex (.inr j) ∧ chartIndex (.inr j) ≤ hi) := by simp [chartIndex]; omega
        simp only [D,active,h,if_false,zero_mul]
  by_cases active : lo < chartIndex p ∧ chartIndex p ≤ hi <;>
    simp [y,M8.Exchange.exchange,Matrix.sub_mulVec,Matrix.mulVec_add,Matrix.mulVec_sub,
      -Matrix.mulVec_mulVec,read,active]

/-- Projecting the reduced parent exchange onto its port flag exchanges the
same interval on arbitrary modular digits, at every tape width. -/
theorem remainderExchange_modular (c : PortCertificate) (hc : c.Checked) (lo hi w : ℕ)
    (x : IntegerMultBounds.Swap.Shear.State Axis (ZMod (prime^w))) :
    let F := reduce (prime^w) c.flag
    let S := reduce (prime^w) (c.span lo hi)
    let y := M8.Exchange.exchange S x
    ∀ p, ((Fᵀ *ᵥ y.1) p, (Fᵀ *ᵥ y.2) p) =
      if lo ≤ pendingIndex p ∧ pendingIndex p < hi then ((Fᵀ *ᵥ x.2) p, (Fᵀ *ᵥ x.1) p)
      else ((Fᵀ *ᵥ x.1) p, (Fᵀ *ᵥ x.2) p) := by
  intro F S y p
  have eq (v : Axis → ZMod (prime^w)) :
      (((reduce (prime^w) c.fullChart)ᵀ) *ᵥ v) (.inr p) = (Fᵀ *ᵥ v) p := rfl
  have bounds : (lo < chartIndex (.inr p) ∧ chartIndex (.inr p) ≤ hi) ↔
      lo ≤ pendingIndex p ∧ pendingIndex p < hi := by simp only [chartIndex]; omega
  simpa only [bounds,eq] using remainderExchange_chart c hc lo hi w x (.inr p)

/-- Descriptor order places the 63 pending digits first and the line last. -/
def remainderAxis : Fin 64 ≃ ChartAxis where
  toFun i := if h : i.val < 63 then .inr (pendingAt ⟨i.val,h⟩) else .inl 0
  invFun := Sum.elim (fun _ => 63) (fun p => ⟨pendingIndex p, by
    have := chartIndex_lt (.inr p)
    simp only [chartIndex] at this
    omega⟩)
  left_inv i := by
    by_cases h : i.val < 63
    · apply Fin.ext
      simp [h,pendingIndex_pendingAt]
    · apply Fin.ext
      have := i.isLt
      simp [h,show i.val = 63 by omega]
  right_inv a := by
    cases a with
    | inl j => simp [Subsingleton.elim j 0]
    | inr p =>
      have bound := chartIndex_lt (.inr p)
      simp only [chartIndex] at bound
      have h : pendingIndex p < 63 := by omega
      change (if h : pendingIndex p < 63 then Sum.inr (pendingAt ⟨pendingIndex p,h⟩) else Sum.inl 0) = Sum.inr p
      rw [dif_pos h, Sum.inr.injEq]
      apply pendingIndex_injective
      exact pendingIndex_pendingAt _

/-- In the tape descriptor's digit order the modular action is the literal
half-open interval exchange, including its behavior at the final line digit. -/
theorem remainderExchange_tapeDigits (c : PortCertificate) (hc : c.Checked)
    (lo hi w : ℕ) (fits : hi ≤ 63) (x : IntegerMultBounds.Swap.Shear.State Axis (ZMod (prime^w))) :
    let read := fun (v : Axis → ZMod (prime^w)) (i : Fin 64) =>
      ((reduce (prime^w) c.fullChart)ᵀ *ᵥ v) (remainderAxis i)
    let y := M8.Exchange.exchange (reduce (prime^w) (c.span lo hi)) x
    ∀ i, (read y.1 i, read y.2 i) =
      if lo ≤ i.val ∧ i.val < hi then (read x.2 i,read x.1 i) else (read x.1 i,read x.2 i) := by
  intro read y i
  have bounds : (lo < chartIndex (remainderAxis i) ∧ chartIndex (remainderAxis i) ≤ hi) ↔
      lo ≤ i.val ∧ i.val < hi := by
    by_cases h : i.val < 63 <;> simp [remainderAxis,h,chartIndex,pendingIndex_pendingAt] <;> omega
  simpa only [bounds] using remainderExchange_chart c hc lo hi w x (remainderAxis i)

open IntegerMultBounds.MathlibTM2.Cover IntegerMultBounds.MathlibTM2.M8.RevMachine
open M8.Stage2Machine.Straight (words)
open ActualAffineScaling (modulus)
open SharedPlacementAlphabet (setTape)

/-- Physically change the cover matrix labels into or out of the idle port's
pending-first coordinate order on the chosen owner tape. -/
theorem remainderChart_runs [M8.Machine.Net] {T : ℕ} (io : Fin T) (c : PortCertificate)
    (hc : c.Checked) (inverse : Bool) :
    let H := c.fullChart.submatrix stageAxis.symm remainderAxis
    let σ := if inverse then H.transpose else H
    ∃ (program : Graph.Block (T+24) prime) (C : ℕ), Blocks.Leading program ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
      v.beforeH = B*prime^(64*(w*64)) → v.Positive →
      ∀ (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2),
        roles.head io = 0 → roles.tape io = sourceWord x →
        let d := words (LabelSchedule.base v w)
        ∃ y : Fin (volume prime v) → ZMod 2,
          LabelPermutation.Transport v B w (fun g => g * reduce (modulus w) σ) (ext x) (ext y) ∧
          let cost := C*volume prime v + 63*LeafCore.coreCost (volume prime v) (w*64)
          GraphContract.Runs program (LabelCall.bank roles v d)
            (LabelCall.bank (setTape roles io (sourceWord y) 0) v d) cost ∧
          ∀ width : ℕ, w*64 ≤ width → (cost : ℝ) ≤
            ((C : ℝ) + 63 * |LeafCore.C| * (width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime v := by
  intro H σ
  have orth : H.transpose * H = 1 := by
    change (c.fullChart.transpose.submatrix remainderAxis stageAxis.symm) * _ = _
    rw [submatrix_mul_equiv,c.fullChart_orthonormal hc,submatrix_one_equiv]
  exact boundedChart_runs io H (isUnit_iff_exists.mpr ⟨_,mul_eq_one_comm.mp orth,orth⟩)
    (fun i j => fullChart_entry c hc (stageAxis.symm i) (remainderAxis j)) inverse

/-- A row of the physically relabelled matrix reads exactly the modular digits
used by the interval descriptor, with the port line at the last position. -/
theorem remainderChart_row (c : PortCertificate) (w : ℕ)
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (r i : Fin 64) :
    (g * reduce (prime^w) (c.fullChart.submatrix stageAxis.symm remainderAxis)) r i =
      ((reduce (prime^w) c.fullChart)ᵀ *ᵥ (fun a => g r (stageAxis a))) (remainderAxis i) := by
  rw [Matrix.mul_apply]
  change _ = ∑ a, (reduce (prime^w) c.fullChart) a (remainderAxis i) * g r (stageAxis a)
  rw [← Equiv.sum_comp stageAxis.symm]
  simp only [Equiv.apply_symm_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- In pending-first tape order the rational remainder projector is a diagonal
interval. This factorization identifies the projector needed at a live cover label. -/
theorem remainderProjector_factor (c : PortCertificate) (lo hi : ℕ) (fits : hi ≤ 63) :
    let H := c.fullChart.submatrix stageAxis.symm remainderAxis
    let D : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i =>
      if lo ≤ i.val ∧ i.val < hi then 1 else 0
    (c.span lo hi).submatrix stageAxis.symm stageAxis.symm = H * D * H.transpose := by
  intro H D
  ext a b
  let weight := fun j : ChartAxis => if lo < chartIndex j ∧ chartIndex j ≤ hi then (1 : ℚ) else 0
  have atDigit (i : Fin 64) : weight (remainderAxis i) = if lo ≤ i.val ∧ i.val < hi then 1 else 0 := by
    have bounds : (lo < chartIndex (remainderAxis i) ∧ chartIndex (remainderAxis i) ≤ hi) ↔
        lo ≤ i.val ∧ i.val < hi := by
      by_cases h : i.val < 63 <;> simp [remainderAxis,h,chartIndex,pendingIndex_pendingAt] <;> omega
    simp only [weight,bounds]
  change (c.span lo hi) _ _ = _
  unfold PortCertificate.span
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [interval, Matrix.mul_diagonal,
    Matrix.transpose_apply,H,D,Matrix.submatrix_apply]
  simp_rw [← atDigit]
  rw [Equiv.sum_comp remainderAxis (fun j => c.fullChart (stageAxis.symm a) j * weight j *
    c.fullChart (stageAxis.symm b) j)]
  conv_rhs => rw [Fintype.sum_sum_type]
  simp only [weight,chartIndex,not_lt_zero',false_and,if_false,mul_zero,zero_mul,Finset.sum_const_zero,zero_add]
  apply Finset.sum_congr rfl
  intro p _
  change _ = c.flag _ p * (if lo < 1+pendingIndex p ∧ 1+pendingIndex p ≤ hi then 1 else 0) * c.flag _ p
  have same : (lo < 1+pendingIndex p ∧ 1+pendingIndex p ≤ hi) ↔
      lo ≤ pendingIndex p ∧ pendingIndex p < hi := by omega
  simp only [same]

/-- After the forward pass relabels a record from g to gH, the cover
normalizer for the diagonal interval gives the parent's conjugated projector. -/
theorem remainderProjector_atLabel (c : PortCertificate) (hc : c.Checked) (lo hi w : ℕ)
    (fits : hi ≤ 63) (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) :
    let H := reduce (prime^w) (c.fullChart.submatrix stageAxis.symm remainderAxis)
    let D : Matrix (Fin 64) (Fin 64) (ZMod (prime^w)) := diagonal fun i =>
      if lo ≤ i.val ∧ i.val < hi then 1 else 0
    let P := reduce (prime^w) ((c.span lo hi).submatrix stageAxis.symm stageAxis.symm)
    g * P * g⁻¹ = (g*H) * D * (g*H)⁻¹ := by
  intro H D P
  let A := c.fullChart.submatrix stageAxis.symm remainderAxis
  let I : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i =>
    if lo ≤ i.val ∧ i.val < hi then 1 else 0
  have chart : Admissible (prime^w) A := by
    intro i j
    have bound : (A i j).den ≤ 2 := (fullChart_entry c hc (stageAxis.symm i) (remainderAxis j)).2
    exact Nat.Coprime.pow_right w ((Nat.coprime_of_lt_prime (A i j).den_pos.ne'
      (bound.trans_lt Shared50ModularControl.prime_odd) Shared50ModularControl.prime_prime).symm)
  have tr : Admissible (prime^w) Aᵀ := fun i j => chart j i
  have di : Admissible (prime^w) I := by
    intro i j
    simp only [I, diagonal_apply]
    split_ifs <;> simp
  have reduced : reduce (prime^w) I = D := by
    ext i j
    simp only [reduce, Matrix.map_apply,I,D,diagonal_apply]
    split_ifs <;> simp [ratMod_zero,ratMod_one]
  have factor : P = H*D*Hᵀ := by
    have h : (c.span lo hi).submatrix stageAxis.symm stageAxis.symm = A*I*Aᵀ :=
      remainderProjector_factor c lo hi fits
    dsimp only [P]
    rw [h,reduce_mul _ (admissible_mul _ chart di) tr, reduce_mul _ chart di,reduced]
    rfl
  have orth : Aᵀ * A = 1 := by
    change (c.fullChart.transpose.submatrix remainderAxis stageAxis.symm) * _ = _
    rw [submatrix_mul_equiv,c.fullChart_orthonormal hc,submatrix_one_equiv]
  have inv : H⁻¹ = Hᵀ := Matrix.inv_eq_right_inv (reduce_inverse _ chart tr (mul_eq_one_comm.mp orth))
  rw [factor,Matrix.mul_inv_rev,inv]
  simp only [Matrix.mul_assoc]

open IntegerMultBounds.Swap.LowerTriangular

/-- The cover normalizer needs a rational pivot factorization even when its
input projector is diagonal. All four triangular factors here are identities. -/
def intervalFactor (m lo hi : ℕ) :
    Factorization Finset.univ Finset.univ (diagonal (fun i : Fin m =>
      if lo ≤ i.val ∧ i.val < hi then (1 : ℚ) else 0)) := by
  let axes := (List.finRange m).filter fun i => decide (lo ≤ i.val ∧ i.val < hi)
  let pivots := axes.map fun i => (i,i)
  have nodup : axes.Nodup := (List.nodup_finRange m).filter _
  refine ⟨1,1,1,1,pivots,lower_one,lower_one,lower_one,lower_one,by simp,by simp,
    by simp,by simp,idOutside_one _,idOutside_one _,by simp,
    by simpa [pivots,List.map_map,Function.comp_def] using nodup,
    by simpa [pivots,List.map_map,Function.comp_def] using nodup,?_⟩
  simp only [Matrix.one_mul, Matrix.mul_one]
  ext i j
  rw [IntegerMultBounds.Swap.PivotRank.pivotMatrix_apply pivots
    (nodup.map (fun _ _ h => congrArg Prod.fst h)), diagonal_apply]
  by_cases same : i = j
  · subst j
    simp [pivots,axes]
  · simp [pivots,axes,same,Ne.symm same]

/-- The diagonal normalizer is admissible at the existing machine prime for
every interval. Neither its projector nor any factor introduces a denominator. -/
theorem intervalFactor_denominators (m lo hi : ℕ) :
    ∀ d ∈ factorizationDenominators (intervalFactor m lo hi), d < prime := by
  intro d hd
  have one : ∀ d ∈ denominators (1 : Matrix (Fin m) (Fin m) ℚ), d = 1 := by
    intro d mem
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp mem
    simp only [Matrix.one_apply]
    split <;> simp
  have diag : ∀ d ∈ denominators (diagonal (fun i : Fin m =>
      if lo ≤ i.val ∧ i.val < hi then (1 : ℚ) else 0)), d = 1 := by
    intro d mem
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp mem
    simp only [diagonal_apply]
    split_ifs <;> simp
  simp only [factorizationDenominators, Finset.mem_union] at hd
  have eq : d = 1 := by rcases hd with (((h|h)|h)|h)|h <;> first | exact diag d h | exact one d h
  simpa only [eq] using Shared50ModularControl.prime_prime.one_lt

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- The cover's good-record test at the routed physical address checks the
leading minors of the original port projector in the incoming label. -/
theorem remainderGood_at (c : PortCertificate) (hc : c.Checked) (lo hi w : ℕ)
    (hw : 0 < w) (fits : hi ≤ 63) (block : ℕ) (g : LabelPadding.Label 64 w) :
    let H := reduce (prime^w) (c.fullChart.submatrix stageAxis.symm remainderAxis)
    let D : LabelPadding.Label 64 w := diagonal fun i =>
      if lo ≤ i.val ∧ i.val < hi then 1 else 0
    let P := reduce (prime^w) ((c.span lo hi).submatrix stageAxis.symm stageAxis.symm)
    let r := hi-lo
    let hr : r ≤ 64 := by dsimp [r]; omega
    IsUnit (g*H).det →
      (LabelProjector.good ((LabelRing.res prime w hw).mapMatrix D) r hr
        (LabelStock.residue 64 w 1 (block*(prime^w)^(64*64)+(LabelAddress.address (g*H)).val)) = true ↔
        ∀ k (hk : k < r), IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk hr) (g*P*g⁻¹)).det) := by
  intro H D P r hr live
  rw [LabelProjector.good_at hw D (g*H) live r hr block]
  have same : g*P*g⁻¹ = (g*H)*D*(g*H)⁻¹ := remainderProjector_atLabel c hc lo hi w fits g
  rw [same]

/-- The diagonal interval charges one pivot for each digit in the interval. -/
theorem intervalDiagonal_rank {m lo hi : ℕ} (fits : hi ≤ m) :
    (diagonal (fun i : Fin m => if lo ≤ i.val ∧ i.val < hi then (1 : ℚ) else 0)).rank = hi-lo := by
  rw [rank_diagonal]
  let E : {i : Fin m // (if lo ≤ i.val ∧ i.val < hi then (1 : ℚ) else 0) ≠ 0} ≃ Fin (hi-lo) :=
    { toFun := fun i => ⟨i.val.val-lo,by
        have h : lo ≤ i.val.val ∧ i.val.val < hi := by simpa using i.property
        omega⟩
      invFun := fun j => ⟨⟨lo+j.val,by omega⟩,by
        have lt := j.isLt
        simp [show lo+j.val < hi by omega]⟩
      left_inv := by
        intro i
        have h : lo ≤ i.val.val ∧ i.val.val < hi := by simpa using i.property
        apply Subtype.ext
        apply Fin.ext
        dsimp
        omega
      right_inv := by intro j; apply Fin.ext; simp }
  exact (Fintype.card_congr E).trans (Fintype.card_fin _)

private theorem intervalDiagonal_idem (m lo hi : ℕ) :
    let D : Matrix (Fin m) (Fin m) ℚ := diagonal fun i => if lo ≤ i.val ∧ i.val < hi then 1 else 0
    D*D = D := by
  intro D
  unfold D
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

open M8.Exchange M8.ReversedExchange IntegerMultBounds.Swap.Shear in
/-- On a live accepted record, the cover's weighted child has exactly the
charged interval width and realizes the incoming port's conjugated exchange. -/
theorem remainderGood_move (c : PortCertificate) (hc : c.Checked) (lo hi w : ℕ)
    (hw : 0 < w) (fits : hi ≤ 63) (block : ℕ) (g : LabelPadding.Label 64 w)
    (α α' : Fin 64 → ZMod (prime^w)) (inv : ∀ i, α i * α' i = 1) :
    let H := reduce (prime^w) (c.fullChart.submatrix stageAxis.symm remainderAxis)
    let P := reduce (prime^w) ((c.span lo hi).submatrix stageAxis.symm stageAxis.symm)
    let D : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i =>
      if lo ≤ i.val ∧ i.val < hi then 1 else 0
    let r := hi-lo
    let hr : r ≤ 64 := by dsimp [r]; omega
    IsUnit (g*H).det →
    LabelProjector.good (reduce prime D) r hr (LabelStock.residue 64 w 1
      (block*(prime^w)^(64*64)+(LabelAddress.address (g*H)).val)) = true →
    ∃ (L L' R R' K : LabelPadding.Label 64 w) (δ δ' : Fin 64 → ZMod (prime^w)),
      GoodForm.UnitLower L ∧ GoodForm.UnitLower L' ∧ GoodForm.UnitLower R ∧ GoodForm.UnitLower R' ∧
      (∀ i, δ i * δ' i = 1) ∧ ∀ s : IntegerMultBounds.Swap.Shear.State (Fin 64) (ZMod (prime^w)),
        transform (diagonal α * L * diagonal α') R'
          (cross (-K) (Weighted.child r (fun i => α i * δ i) (fun i => α' i * δ' i)
            (cross K (transform (diagonal α * L' * diagonal α') R s)))) =
          transform (diagonal α) 1 (revExchangeOf (rev 64) (g*P*g⁻¹) (transform (diagonal α') 1 s)) := by
  intro H P D r hr live accepted
  have rank : D.rank = r := intervalDiagonal_rank (by omega : hi ≤ 64)
  have idem := intervalDiagonal_idem 64 lo hi
  have result := LabelProjector.good_move_at hw D idem (intervalFactor 64 lo hi)
    (intervalFactor_denominators 64 lo hi) (rank.trans_le hr) (g*H) live block α α' inv
    (by simpa only [rank] using accepted)
  have reduced : reduce (prime^w) D = diagonal (fun i : Fin 64 =>
      if lo ≤ i.val ∧ i.val < hi then (1 : ZMod (prime^w)) else 0) := by
    ext i j
    simp only [reduce, Matrix.map_apply,D,diagonal_apply]
    split_ifs <;> simp [ratMod_zero,ratMod_one]
  rw [remainderProjector_atLabel c hc lo hi w fits g]
  simpa only [rank,reduced,H] using result

/-- In physical scan order the number of live idle records sent to fallback
has the cover's inverse-prime bound, uniformly in width and block count. -/
theorem remainderFallback_count (lo hi w blocks : ℕ) (fits : hi ≤ 63) :
    let r := hi-lo
    let hr : r ≤ 64 := by dsimp [r]; omega
    let D : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if lo ≤ i.val ∧ i.val < hi then 1 else 0
    let box := (prime^(w+1))^(64*64)
    (List.range (blocks*box)).countP (fun j => Cover.Fallback.fallbackBit hr (reduce (prime^(w+1)) D)
      (Cover.Fallback.physicalLabel 64 (w+1) j)) * prime ≤
      (∑ k ∈ Finset.range r, (k+1)*(64+1)) * (blocks*box) := by
  intro r hr D box
  have rank : D.rank = r := intervalDiagonal_rank (by omega : hi ≤ 64)
  obtain ⟨g,unit,good⟩ := LabelProjector.residue_witness (by omega : 0 < w+1) D
    (intervalDiagonal_idem 64 lo hi) (intervalFactor 64 lo hi) (intervalFactor_denominators 64 lo hi)
    (rank.trans_le hr)
  apply Cover.Fallback.fallbackRecordCount w r blocks hr _ g unit
  simpa only [rank] using good

/-- The idle owner's other digits and all its spectator positions are exactly
the middle gap and inherited fields of the parent's recursive rank descriptor. -/
theorem remainderSpectators (v : Descriptor) (rows w : ℕ)
    (splitRows : v.rows = 142080*rows) (e : ℕ × ℕ) (he : e ∈ BitHosting.remainderIntervals) :
    let W := v.beforeRows*rows*v.beforeH*v.between*v.afterD
    spectators (phaseIntervalChild e.1 e.2 w W 64) =
      spectators (rankDescriptor prime ((e.2-e.1)*w) ((64-(e.2-e.1))*w) (role v 142080)) := by
  intro W
  obtain ⟨ordered, fits, _⟩ := BitHosting.remainder_counts e he
  have gap : 64-(e.2-e.1) = 64-e.2+e.1 := by omega
  simp only [spectators,phaseIntervalChild,rankDescriptor,role,W,splitRows,
    Nat.mul_div_cancel_left _ (by decide : 0 < 142080),one_mul,gap,
    Nat.mul_comm (64-e.2+e.1) w,pow_mul,pow_add]
  ring

/-- The parent's recursive rank address and the idle interval address have the
same packed offset both before and after the exchange. -/
theorem remainderPacked_swap (v : Descriptor) (rows w : ℕ)
    (splitRows : v.rows = 142080*rows) (e : ℕ × ℕ) (he : e ∈ BitHosting.remainderIntervals) :
    let child := phaseIntervalChild e.1 e.2 w (v.beforeRows*rows*v.beforeH*v.between*v.afterD) 64
    let parentChild := rankDescriptor prime ((e.2-e.1)*w) ((64-(e.2-e.1))*w) (role v 142080)
    let chart := changeLayout child parentChild rfl (remainderSpectators v rows w splitRows e he)
    ∀ a, (packActive parentChild (RecursiveInterchangeScaling.index
        (Shared50RecursiveNodeTranspose.swapAddress (chart a)))).val =
      (packActive child (RecursiveInterchangeScaling.index
        (Shared50RecursiveNodeTranspose.swapAddress a))).val := by
  intro child parentChild chart a
  exact CopyChildLayout.packActive_change child parentChild rfl
    (remainderSpectators v rows w splitRows e he) (Shared50RecursiveNodeTranspose.swapAddress a)

/-- A word representing the parent's rank child still represents it after
the physical exchange, at every parent address. -/
theorem remainderTranspose_represents (v : Descriptor) (rows w : ℕ)
    (splitRows : v.rows = 142080*rows) (e : ℕ × ℕ) (he : e ∈ BitHosting.remainderIntervals) :
    let child := phaseIntervalChild e.1 e.2 w (v.beforeRows*rows*v.beforeH*v.between*v.afterD) 64
    let parentChild := rankDescriptor prime ((e.2-e.1)*w) ((64-(e.2-e.1))*w) (role v 142080)
    let chart := changeLayout child parentChild rfl (remainderSpectators v rows w splitRows e he)
    ∀ (x : Fin (volume prime child) → ZMod 2) (p : Fin (volume prime parentChild) → ZMod 2),
      (∀ a, x (RecursiveInterchangeScaling.index a) = p (RecursiveInterchangeScaling.index (chart a))) →
      ∀ a, Shared50RecursiveNodeRows.transpose (one_dvd _) x (RecursiveInterchangeScaling.index a) =
        Shared50RecursiveNodeRows.transpose (one_dvd _) p (RecursiveInterchangeScaling.index (chart a)) := by
  intro child parentChild chart x p reads a
  let b := Shared50RecursiveNodeTranspose.swapAddress a
  have physical := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) (one_dvd _) x b
  have logical := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) (one_dvd _) p (chart b)
  exact physical.trans ((reads b).trans logical.symm)

/-- With its headers represented, one fixed program exchanges the idle interval on
the owner's tape, preserving both exterior slices even for an empty interval. -/
theorem remainderInterval_runs [M8.Machine.Net] {t w W : ℕ}
    (e : ℕ × ℕ) (hW : 0 < W)
    (caller : Tapes t prime) (headers : Fin 6 → Fin t) (src : Fin t)
    (hs : Fin 6 → List Bool) :
    let child := phaseIntervalChild e.1 e.2 w W 64
    RecursiveDimensionBank.Headers child hs →
    (∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i)) →
    (∀ i, caller.head (headers i) = 1) →
    ∀ x : Fin (volume prime child) → ZMod 2,
    caller.tape src = sourceWord x → caller.head src = 0 →
    ∃ y : Fin (volume prime child) → ZMod 2,
      HoareTime (program headers src) (fun z => z = input caller)
        (fun z => z = input (SharedPlacementAlphabet.setTape caller src (sourceWord y) 0))
        (cost child hs) ∧
      y = Shared50RecursiveNodeRows.transpose (one_dvd _) x ∧
      ∀ a b h d u v j,
        y (RecursiveInterchangeScaling.index (intervalAddress 64 a b d h u v j)) =
        x (RecursiveInterchangeScaling.index (intervalAddress 64 a b h d u v j)) := by
  intro child valid words heads x data origin
  have pos := pow_pos Shared50ModularControl.prime_prime.pos w
  have positive : child.Positive := ⟨Nat.zero_lt_one, Nat.zero_lt_one, pow_pos pos _,
    pow_pos pos _, Nat.mul_pos (pow_pos pos _) hW⟩
  exact ⟨_, M8.Machine.ArbitraryWidthOriginalTotalRun.runs caller headers src child hs
    positive valid words heads x data origin, rfl, intervalAddress_transpose 64 x⟩

/-- Compute the idle child's headers, then run its exchange on the same owner.
The arithmetic bank takes the binary width, spectator count and fixed interval length. -/
theorem remainderPrepared_runs [M8.Machine.Net] {t w W : ℕ}
    (e : ℕ × ℕ) (he : e ∈ BitHosting.remainderIntervals) (hw : 0 < w) (hW : 0 < W)
    (caller : Tapes t prime) (src : Fin t)
    (x : Fin (volume prime (phaseIntervalChild e.1 e.2 w W 64)) → ZMod 2)
    (payload : caller.tape src = sourceWord x) (head : caller.head src = 0) :
    let child := phaseIntervalChild e.1 e.2 w W 64
    let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child i)
    let headers := fun i => Fin.castAdd t (phaseHeaderSlots i)
    let site := Fin.natAdd 24 src
    let setup := M8.Machine.ArbitraryWidthOriginalRun.extendBanks
      (extend (extend (extend (phaseHeaderProgram e.1 e.2 64) t) 16) 19)
    ∃ y : Fin (volume prime child) → ZMod 2,
      HoareTime (seq setup (program headers site))
        (fun z => z = input ((phaseHeaderInput e.1 e.2 w W).append caller))
        (fun z => z = input (SharedPlacementAlphabet.setTape
          ((phaseHeaderOutput e.1 e.2 w W 64).append caller) site (sourceWord y) 0))
        ((2*(24*64+333)+250)*((prime^w)^128*W) + 1 + cost child hs) ∧
      y = Shared50RecursiveNodeRows.transpose (one_dvd _) x ∧
      ∀ a b h d u v j,
        y (RecursiveInterchangeScaling.index (intervalAddress 64 a b d h u v j)) =
        x (RecursiveInterchangeScaling.index (intervalAddress 64 a b h d u v j)) := by
  intro child hs headers site setup
  obtain ⟨ordered, fits, _⟩ := BitHosting.remainder_counts e he
  obtain ⟨build, valid, slots⟩ := intervalHeader_runs (by decide : 0 < 64) ordered
    (show e.2 ≤ 64 by omega) hw hW
  let output := phaseHeaderOutput e.1 e.2 w W 64
  obtain ⟨y, move, action⟩ := remainderInterval_runs e hW (output.append caller) headers site hs valid
    (fun i => by simpa [headers,Tapes.append,output] using (slots i).2)
    (fun i => by simpa [headers,Tapes.append,output] using (slots i).1)
    x (by simpa [site,Tapes.append] using payload) (by simpa [site,Tapes.append] using head)
  have prepare := M8.Machine.ArbitraryWidthOriginalRun.extend_banks_hoare
    (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq build caller)
      (FixedHeaderBankCopy.empty 16)) M8.Machine.ArbitraryWidthHighPrepareShared.privateInput)
  exact ⟨y, prepare.seq move, action⟩

/-- The prepared interval run is a composable stage on the permanent owner bank.
Only the selected owner is updated, by exactly the child transpose. -/
theorem remainderOwner_stage [M8.Machine.Net] {k w W : ℕ} (src : Fin k)
    (e : ℕ × ℕ) (he : e ∈ BitHosting.remainderIntervals) (hw : 0 < w) (hW : 0 < W) :
    let child := phaseIntervalChild e.1 e.2 w W 64
    let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child i)
    ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := volume prime child)),
      stage.cost = (2*(24*64+333)+250)*((prime^w)^128*W) + 1 + cost child hs ∧
      ∀ data, stage.transform data = Function.update data src
        (Shared50RecursiveNodeRows.transpose (one_dvd _) (data src)) := by
  intro child hs
  let transform := fun data : Fin k → Fin (volume prime child) → ZMod 2 =>
    Function.update data src (Shared50RecursiveNodeRows.transpose (one_dvd _) (data src))
  let initial := phaseHeaderInput e.1 e.2 w W
  let finalBank := phaseHeaderOutput e.1 e.2 w W 64
  let bank := fun (h : Tapes 24 prime) (owners : Tapes k prime) => input (h.append owners)
  obtain ⟨slots,frame⟩ := intervalPrepared_frame (k := k)
  have run (data : Fin k → Fin (volume prime child) → ZMod 2) :=
    remainderPrepared_runs e he hw hW (phaseOwners data) src (data src) (sourceWord_cast (v := child) rfl (data src)).symm rfl
  let machineOf {t q b : ℕ} {g : Program t q prime} {pre post : Tapes t prime → Prop}
      (_ : HoareTime g pre post b) := g
  let machine := machineOf (run 0).choose_spec.1
  refine ⟨{ tapes := _, states := _, program := machine, transform := transform,
            input := fun data => bank initial (phaseOwners data),
            output := fun data => bank finalBank (phaseOwners (transform data)),
            slots := slots, slots_injective := slots.injective,
            metadata := SharedBank.strip (bank initial (SharedBank.empty k prime)) slots,
            cost := _, input_payload := fun data => (frame _ _).1,
            output_payload := fun data => (frame _ _).1,
            strip_input := fun data => (frame _ _).2, realizes := ?_ },rfl,fun _ => rfl⟩
  intro data
  obtain ⟨y,step,rfl,_⟩ := run data
  rw [SharedPlacementAlphabet.setTape_append_right] at step
  have updated : setTape (phaseOwners data) src
      (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) (data src))) 0 =
      phaseOwners (transform data) := by
    rw [show sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) (data src)) = _ from sourceWord_cast (v := child) rfl (Shared50RecursiveNodeRows.transpose (one_dvd _) (data src))]
    apply congrArg₂ Tapes.mk <;> funext j <;> by_cases eq : j = src <;>
      simp [phaseOwners,transform,eq]
  rw [updated] at step
  exact step

/-- A chart pass exposes the same permanent owner interface as the idle child,
even when its private tape count depends on the compiled block. -/
theorem remainderChart_stage [M8.Machine.Net] {k : ℕ} (src : Fin k) (c : PortCertificate)
    (hc : c.Checked) (inverse : Bool) :
    let H := c.fullChart.submatrix stageAxis.symm remainderAxis
    let σ := if inverse then H.transpose else H
    ∃ C : ℕ, ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
      v.beforeH = B*prime^(64*(w*64)) → v.Positive →
      ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := volume prime v)),
        stage.cost = C*volume prime v + 63*LeafCore.coreCost (volume prime v) (w*64) ∧
        ∀ data, (∀ j, j ≠ src → stage.transform data j = data j) ∧
          LabelPermutation.Transport v B w (fun g => g * reduce (modulus w) σ)
            (ext (data src)) (ext (stage.transform data src)) := by
  intro H σ
  obtain ⟨block,C,leading,runs⟩ := remainderChart_runs src c hc inverse
  refine ⟨C,?_⟩
  intro v w B hw hb shape positive
  let result := fun data : Fin k → Fin (volume prime v) → ZMod 2 =>
    runs v w B hw hb shape positive (phaseOwners data) (data src) rfl
      (sourceWord_cast (v := v) rfl (data src)).symm
  let moved := fun data => (result data).choose
  let transform := fun data => Function.update data src (moved data)
  let slots := fun i => block.slots (Fin.castAdd 24 i)
  let d := words (LabelSchedule.base v w)
  let bank := fun (roles : Tapes k prime) => SharedBankStageInput.raw (LabelCall.bank roles v d) block.tapes
  have updated (data) : setTape (phaseOwners data) src (sourceWord (moved data)) 0 =
      phaseOwners (transform data) := by
    rw [show sourceWord (moved data) = _ from sourceWord_cast (v := v) rfl (moved data)]
    apply congrArg₂ Tapes.mk <;> funext j <;> by_cases eq : j = src <;>
      simp [phaseOwners,transform,eq]
  refine ⟨{ tapes := _, states := _, program := block.program, transform := transform,
            input := fun data => bank (phaseOwners data),
            output := fun data => bank (phaseOwners (transform data)),
            slots := slots, slots_injective := fun i j eq => Fin.ext ((leading (Fin.castAdd 24 i)).symm.trans ((congrArg Fin.val eq).trans (leading (Fin.castAdd 24 j)))),
            metadata := SharedBank.strip (bank (SharedBank.empty k prime)) slots,
            cost := _, input_payload := fun _ => copyRoute_payload block leading _ v d,
            output_payload := fun _ => copyRoute_payload block leading _ v d,
            strip_input := fun _ => routePrivate block leading _ _ v d, realizes := ?_ },rfl,?_⟩
  · intro data
    have run := (result data).choose_spec.2.1
    change GraphContract.Runs block _ (LabelCall.bank (setTape _ src (sourceWord (moved data)) 0) v d) _ at run
    rwa [updated] at run
  · intro data
    exact ⟨fun j off => Function.update_of_ne off .., by
      simpa only [transform,Function.update_self] using (result data).choose_spec.1⟩

private theorem remainderOwner_flat [M8.Machine.Net] {k w W N : ℕ} (src : Fin k)
    (e : ℕ × ℕ) (he : e ∈ BitHosting.remainderIntervals) (hw : 0 < w) (hW : 0 < W)
    (size : volume prime (phaseIntervalChild e.1 e.2 w W 64) = N) :
    let child := phaseIntervalChild e.1 e.2 w W 64
    let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child i)
    ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := N)),
      stage.cost = (2*(24*64+333)+250)*((prime^w)^128*W) + 1 + cost child hs ∧
      ∀ data, stage.transform data = Function.update data src (fun i =>
        Shared50RecursiveNodeRows.transpose (one_dvd child.rows)
          (fun j => data src (Fin.cast size j)) (Fin.cast size.symm i)) := by
  subst N
  exact remainderOwner_stage src e he hw hW

/-- Run the forward label pass, interval child and inverse label pass on one
owner. The label is part of the spectator range throughout the child run. -/
theorem routedRemainder_stage [M8.Machine.Net] {k : ℕ} (src : Fin k)
    (c : PortCertificate) (hc : c.Checked) (e : ℕ × ℕ) (he : e ∈ BitHosting.remainderIntervals) :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let v : Descriptor := ⟨(prime^w)^128,1,B*prime^(64*(w*64)),0,1,K⟩
      let V := volume prime v
      let child := phaseIntervalChild e.1 e.2 w W 64
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child i)
      let H := c.fullChart.submatrix stageAxis.symm remainderAxis
      ∃ (size : volume prime child = V) (stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V))),
        stage.cost ≤ C*V + 126*LeafCore.coreCost V (w*64) + cost child hs + 3 ∧
        ∀ data, (∀ j, j ≠ src → stage.transform data j = data j) ∧
          ∃ y : Fin V → ZMod 2,
            LabelPermutation.Transport v B w (fun g => g * reduce (modulus w) H) (ext (data src)) (ext y) ∧
            LabelPermutation.Transport v B w (fun g => g * reduce (modulus w) H.transpose)
              (ext (fun i => Shared50RecursiveNodeRows.transpose (one_dvd child.rows)
                (fun j => y (Fin.cast size j)) (Fin.cast size.symm i))) (ext (stage.transform data src)) := by
  obtain ⟨A,enter⟩ := remainderChart_stage src c hc false
  obtain ⟨D,leave⟩ := remainderChart_stage src c hc true
  refine ⟨A+(2*(24*64+333)+250)+D,?_⟩
  intro w B K hw hb hk W v V child hs H
  have pos := Shared50ModularControl.prime_prime.pos
  have hW : 0 < W := by dsimp [W]; positivity
  have vp : v.Positive := ⟨pow_pos (pow_pos pos _) _,Nat.zero_lt_one,Nat.mul_pos hb (pow_pos pos _),Nat.zero_lt_one,hk⟩
  have flat : V = (prime^w)^128*W := by simp [V,v,volume,W,Nat.mul_assoc]
  obtain ⟨ordered,fit,_⟩ := BitHosting.remainder_counts e he
  have size : volume prime child = V := (intervalChild_volume ordered (show e.2 ≤ 64 by omega) w W).trans flat.symm
  obtain ⟨s,bs,es⟩ := enter v w B hw hb rfl vp
  obtain ⟨m,bm,em⟩ := remainderOwner_flat src e he hw hW size
  obtain ⟨t,bt,et⟩ := leave v w B hw hb rfl vp
  refine ⟨size,SharedBankStage.compose (SharedBankStage.compose s m) t,?_,?_⟩
  · change s.cost+m.cost+1+t.cost+1 ≤ _
    rw [bs,bm,bt,← flat]
    dsimp only [V,child,hs]
    simp only [Nat.add_mul]
    omega
  · intro data
    let y := s.transform data
    have afterChild := em y
    refine ⟨?_,y src,(es data).2,?_⟩
    · intro j off
      exact ((et (m.transform y)).1 j off).trans (by rw [afterChild,Function.update_of_ne off]; exact (es data).1 j off)
    · have out := (et (m.transform y)).2
      rw [afterChild,Function.update_self] at out
      simpa only [SharedBankStage.compose,y,afterChild,H,ite_true, Bool.true_eq] using out

end IntegerMultBounds.MathlibTM2.M6.BitNode
