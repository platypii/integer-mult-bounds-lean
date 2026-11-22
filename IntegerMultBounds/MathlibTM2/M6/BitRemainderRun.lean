module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordMasks
public import IntegerMultBounds.MathlibTM2.Cover.ProjectorWitness
public import IntegerMultBounds.MathlibTM2.M6.BitCopyLabel
public import IntegerMultBounds.MathlibTM2.M6.BitCopyChildLayout
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalTotalRun

/-! Physical interchange of the unhosted interval on an idle owner's flag coordinates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitHosting
open BitOccurrences

theorem idleRank_eq : ∀ i : Fin 9, (idleRanks 4).getD i.val 0 =
    7 * idleTarget i.val - 7 * idleSource i.val := by decide +kernel

/-- Physical idle intervals realize the charged rank list. -/
theorem remainderWidths_perm :
    (remainderIntervals.map fun e => e.2 - e.1).Perm remainders := by
  apply List.Perm.trans _ remainders_perm
  apply List.Perm.of_eq
  simp only [remainderIntervals, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro i hi
  apply List.map_congr_left
  intro k _
  rw [idleRank_eq ⟨i, List.mem_range.mp hi⟩]
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

private theorem chart_admissible (c : PortCertificate) (hc : c.Checked) (w : ℕ) :
    Admissible (prime^w) c.fullChart := by
  intro i j
  exact Nat.Coprime.pow_right w ((Nat.coprime_of_lt_prime (c.fullChart i j).den_pos.ne'
    ((fullChart_entry c hc i j).2.trans_lt Shared50ModularControl.prime_odd)
    Shared50ModularControl.prime_prime).symm)

/-- The reduced port chart has a right inverse on chart coordinates. -/
theorem reducedChart_orthonormal (c : PortCertificate) (hc : c.Checked) (w : ℕ) :
    let F := reduce (prime^w) c.fullChart
    Fᵀ * F = 1 := by
  intro F
  have chart := chart_admissible c hc w
  change reduce (prime^w) c.fullChartᵀ * reduce (prime^w) c.fullChart = 1
  have chartT : Admissible (prime^w) c.fullChartᵀ := fun i j => chart j i
  rw [← reduce_mul _ chartT chart,c.fullChart_orthonormal hc,reduce_one]

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
  have chart := chart_admissible c hc w
  have flag : Admissible m c.flag := fun i j => chart i (.inr j)
  let J := reduce m c.flag
  have orth := reducedChart_orthonormal c hc w
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

theorem remainderChart_reduced (c : PortCertificate) (hc : c.Checked) (w : ℕ) :
    let A := c.fullChart.submatrix stageAxis.symm remainderAxis
    let H := reduce (prime^w) A
    Admissible (prime^w) A ∧ H*Hᵀ = 1 := by
  intro A H
  have chart : Admissible (prime^w) A := by
    intro i j
    have bound : (A i j).den ≤ 2 := (fullChart_entry c hc (stageAxis.symm i) (remainderAxis j)).2
    exact Nat.Coprime.pow_right w ((Nat.coprime_of_lt_prime (A i j).den_pos.ne'
      (bound.trans_lt Shared50ModularControl.prime_odd) Shared50ModularControl.prime_prime).symm)
  have tr : Admissible (prime^w) Aᵀ := fun i j => chart j i
  have orth : Aᵀ * A = 1 := by
    change (c.fullChart.transpose.submatrix remainderAxis stageAxis.symm) * _ = _
    rw [submatrix_mul_equiv,c.fullChart_orthonormal hc,submatrix_one_equiv]
  exact ⟨chart,reduce_inverse _ chart tr (mul_eq_one_comm.mp orth)⟩

/-- Use two rows of the physical chart matrix as the active fields. One
interval swap between these rows, followed by the inverse chart, realizes
the port exchange and restores every spectator row even on singular matrices. -/
theorem remainderChart_twoRows (c : PortCertificate) (hc : c.Checked)
    (lo hi w : ℕ) (fits : hi ≤ 63) (g : LabelPadding.Label 64 w)
    (h d : Fin 64) (apart : h ≠ d) :
    let H := reduce (prime^w) (c.fullChart.submatrix stageAxis.symm remainderAxis)
    let charted := g*H
    let swapped : LabelPadding.Label 64 w := fun r i =>
      if lo ≤ i.val ∧ i.val < hi then charted (Equiv.swap h d r) i else charted r i
    let fields := (fun a => g h (stageAxis a), fun a => g d (stageAxis a))
    let y := M8.Exchange.exchange (reduce (prime^w) (c.span lo hi)) fields
    swapped*Hᵀ = fun r j => if r = h then y.1 (stageAxis.symm j) else
      if r = d then y.2 (stageAxis.symm j) else g r j := by
  intro H charted swapped fields y
  let out : LabelPadding.Label 64 w := fun r j => if r = h then y.1 (stageAxis.symm j) else
    if r = d then y.2 (stageAxis.symm j) else g r j
  have read : ∀ r i, (out*H) r i = swapped r i := by
    intro r i
    have digits := remainderExchange_tapeDigits c hc lo hi w fits fields i
    rw [show (out*H) r i = _ from remainderChart_row c w out r i]
    by_cases a : r = h
    · subst r
      by_cases live : lo ≤ i.val ∧ i.val < hi <;>
        simpa [live,out,swapped,charted,H,remainderChart_row,fields,y] using congrArg Prod.fst digits
    by_cases b : r = d
    · subst r
      by_cases live : lo ≤ i.val ∧ i.val < hi <;>
        simpa [live,out,apart.symm,swapped,charted,H,remainderChart_row,fields,y] using congrArg Prod.snd digits
    simp [out,a,b,swapped,charted,H,Equiv.swap_apply_of_ne_of_ne a b,remainderChart_row]
  change swapped*Hᵀ = out
  rw [← show out*H = swapped from Matrix.ext read,Matrix.mul_assoc,(remainderChart_reduced c hc w).2,Matrix.mul_one]

def placeRemainderRow : Fin 128 ⊕ Fin (64*64) → Fin 128 ⊕ Fin (64*64)
    | .inl j =>
      let p := (@finProdFinEquiv 2 64).symm j
      .inr (finProdFinEquiv (p.2,Fin.castAdd 62 p.1))
    | .inr j =>
      let p := (@finProdFinEquiv 64 64).symm j
      Fin.addCases (m := 2) (n := 62) (fun r => .inl (finProdFinEquiv (r,p.1)))
        (fun _ => .inr j) p.2

/-- Exchange the external pair of fields with rows zero and one of a
column-major label. Applying the same placement after the chart exposes
the two charted fields contiguously for the interval child. -/
def remainderRowPlacement : Equiv.Perm (Fin 128 ⊕ Fin (64*64)) :=
  have twice : Function.Involutive placeRemainderRow := by
    intro j
    cases j with
    | inl j =>
      obtain ⟨⟨r,i⟩,rfl⟩ := (@finProdFinEquiv 2 64).surjective j
      simp [placeRemainderRow]
    | inr j =>
      obtain ⟨⟨i,r⟩,rfl⟩ := (@finProdFinEquiv 64 64).surjective j
      induction r using Fin.addCases (m := 2) (n := 62) with
      | left r => simp [placeRemainderRow]
      | right r => simp [placeRemainderRow]
  ⟨placeRemainderRow,placeRemainderRow,twice,twice⟩

@[simp] theorem remainderRowPlacement_field (r : Fin 2) (i : Fin 64) :
    remainderRowPlacement (.inl (finProdFinEquiv (r,i))) =
      .inr (finProdFinEquiv (i,Fin.castAdd 62 r)) := by
  change placeRemainderRow (.inl (finProdFinEquiv (r,i))) = _
  simp [placeRemainderRow]

@[simp] theorem remainderRowPlacement_spectator (r : Fin 62) (i : Fin 64) :
    remainderRowPlacement (.inr (finProdFinEquiv (i,Fin.natAdd 2 r))) =
      .inr (finProdFinEquiv (i,Fin.natAdd 2 r)) := by
  change placeRemainderRow (.inr (finProdFinEquiv (i,Fin.natAdd 2 r))) = _
  simp [placeRemainderRow]

/-- Conjugating the external interval exchange by placement swaps the same
interval on label rows zero and one and restores every external field. -/
theorem remainderRowPlacement_interval (lo hi : ℕ) :
    let fieldSwap : Fin 128 ⊕ Fin (64*64) → Fin 128 ⊕ Fin (64*64)
      | .inl j =>
        let p := (@finProdFinEquiv 2 64).symm j
        if lo ≤ p.2.val ∧ p.2.val < hi then .inl (finProdFinEquiv (Equiv.swap 0 1 p.1,p.2)) else .inl j
      | .inr j => .inr j
    ∀ j, remainderRowPlacement (fieldSwap (remainderRowPlacement j)) =
      match j with
      | .inl f => .inl f
      | .inr l =>
        let p := (@finProdFinEquiv 64 64).symm l
        if lo ≤ p.1.val ∧ p.1.val < hi then .inr (finProdFinEquiv (p.1,Equiv.swap 0 1 p.2)) else .inr l := by
  intro fieldSwap j
  change placeRemainderRow (fieldSwap (placeRemainderRow j)) = _
  cases j with
  | inl f =>
    obtain ⟨⟨r,i⟩,rfl⟩ := (@finProdFinEquiv 2 64).surjective f
    simp [placeRemainderRow,fieldSwap]
  | inr l =>
    obtain ⟨⟨i,r⟩,rfl⟩ := (@finProdFinEquiv 64 64).surjective l
    induction r using Fin.addCases (m := 2) (n := 62) with
    | left r =>
      simp only [placeRemainderRow,Equiv.symm_apply_apply,Fin.addCases_left,fieldSwap]
      fin_cases r <;> by_cases live : lo ≤ i.val ∧ i.val < hi <;>
        simp [placeRemainderRow,fieldSwap,live,Equiv.swap_apply_def]
    | right r =>
      have h0 : Fin.natAdd 2 r ≠ (0 : Fin 64) := by intro h; have := congrArg Fin.val h; simp at this
      have h1 : Fin.natAdd 2 r ≠ (1 : Fin 64) := by intro h; have := congrArg Fin.val h; change 2+r.val = 1 at this; omega
      simp [fieldSwap,placeRemainderRow,Equiv.swap_apply_of_ne_of_ne h0 h1]

section
local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩

/-- The same packed address is a chart prefix followed by a column-major
matrix label. This applies to the output digits of placement as well as
to the input of the inverse placement. -/
theorem remainderPlacement_chartAddress {w : ℕ} (b : ℕ)
    (digits : Fin (128+64*64) → ZMod (prime^w)) :
    let M := prime^w
    let fields := fun i : Fin 128 => digits (Fin.castAdd (64*64) i)
    let g : LabelPadding.Label 64 w := fun r i => digits (Fin.natAdd 128 (finProdFinEquiv (i,r)))
    b*prime^((128+64*64)*w)+(FlatCoordinateLayout.rank digits).val =
      (b*M^128+(FlatCoordinateLayout.rank fields).val)*prime^(64*(w*64))+
        (LabelAddress.address g).val := by
  intro M fields g
  let cols := M8.AtomOps.refine (Route.cols g)
  have split : digits = Fin.addCases (motive := fun _ => ZMod M) fields cols := by
    funext j
    induction j using Fin.addCases with
    | left i => simp [fields]
    | right i =>
      obtain ⟨⟨c,r⟩,rfl⟩ := (@finProdFinEquiv 64 64).surjective i
      simp [cols,M8.AtomOps.refine,Route.cols,g]
  have suffix : M^(64*64) = prime^(64*(w*64)) := by
    rw [← pow_mul]; congr 1; ring
  have total : prime^((128+64*64)*w) = M^128*M^(64*64) := by
    rw [← pow_add,← pow_mul,Nat.mul_comm w]
  rw [total,show (FlatCoordinateLayout.rank digits).val = _ from
    (congrArg (fun f : Fin (128+64*64) → ZMod M => (FlatCoordinateLayout.rank f).val) split).trans
      (ArbitraryWidthSliceTranspose.rank_append fields cols),← suffix,Nat.add_mul,Nat.mul_assoc,Nat.add_assoc]
  rfl

/-- Read the physical chart output directly at the address used by the
placement schedule. The chart leaves the two external fields in the prefix. -/
theorem remainderPlacement_chartRead {v : Descriptor} {w B : ℕ} {x y : ℕ → ZMod 2}
    {f : LabelPadding.Label 64 w → LabelPadding.Label 64 w}
    (transport : LabelPermutation.Transport v (B*(prime^w)^128) w f x y)
    (a : Fin v.beforeRows) (r : Fin v.rows) (b : Fin B) (h d : Fin (prime^v.width))
    (mid : Fin v.between) (j : Fin v.afterD) (digits : Fin (128+64*64) → ZMod (prime^w)) :
    let fields := fun i : Fin 128 => digits (Fin.castAdd (64*64) i)
    let g : LabelPadding.Label 64 w := fun row i => digits (Fin.natAdd 128 (finProdFinEquiv (i,row)))
    let out := Fin.addCases (motive := fun _ => ZMod (prime^w)) fields (M8.AtomOps.refine (Route.cols (f g)))
    let cell := fun u : Fin (128+64*64) → ZMod (prime^w) => RecursiveInterchangeLayout.index prime v
      a r (b.val*prime^((128+64*64)*w)+(FlatCoordinateLayout.rank u).val) h mid d j
    y (cell out) = x (cell digits) := by
  intro fields g out cell
  let chartPrefix := finProdFinEquiv (b,FlatCoordinateLayout.rank fields)
  have bound : b.val*(prime^w)^128+(FlatCoordinateLayout.rank fields).val < B*(prime^w)^128 := by
    simpa [chartPrefix,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using chartPrefix.isLt
  have read := transport g a a.isLt r r.isLt _ bound h h.isLt mid mid.isLt d d.isLt j j.isLt
  dsimp only [cell]
  rw [remainderPlacement_chartAddress b.val out,remainderPlacement_chartAddress b.val digits]
  simpa only [out,Fin.addCases_left,Fin.addCases_right,M8.AtomOps.refine,Equiv.symm_apply_apply,Route.cols] using read

/-- In interval order the whole label is a spectator. Packing it after the
two fields gives the very same offset as the recursive child's descriptor. -/
theorem remainderPlacement_childAddress {lo hi w K : ℕ}
    (a b : Fin lo → ZMod (prime^w)) (h d : Fin (hi-lo) → ZMod (prime^w))
    (u v : Fin (64-hi) → ZMod (prime^w)) (g : LabelPadding.Label 64 w) (t : Fin K) :
    let fields := Fin.addCases (Fin.addCases (Fin.addCases a h) u) (Fin.addCases (Fin.addCases b d) v)
    let digits := Fin.addCases fields (M8.AtomOps.refine (Route.cols g))
    let tail := finProdFinEquiv (LabelAddress.address g,t)
    (FlatCoordinateLayout.index digits t).val =
      (RecursiveInterchangeScaling.index (intervalAddress 64 a b h d u v tail)).val := by
  intro fields digits tail
  rw [intervalAddress_index]
  simp only [FlatCoordinateLayout.index_val,digits,ArbitraryWidthSliceTranspose.rank_append,
    tail,finProdFinEquiv_apply_val,LabelAddress.address,fields]
  ring

/-- The interval child's transpose gives the packed owner read on both sides
of the exchange, with the same independent matrix label and trailing cell. -/
theorem remainderPlacement_childRead {lo hi w K : ℕ}
    (x : Fin (volume prime (phaseIntervalChild lo hi w ((prime^w)^(64*64)*K) 64)) → ZMod 2)
    (a b : Fin lo → ZMod (prime^w)) (h d : Fin (hi-lo) → ZMod (prime^w))
    (u v : Fin (64-hi) → ZMod (prime^w)) (g : LabelPadding.Label 64 w) (t : Fin K) :
    let cell := fun (h d : Fin (hi-lo) → ZMod (prime^w)) => FlatCoordinateLayout.index
      (Fin.addCases (Fin.addCases (Fin.addCases (Fin.addCases a h) u) (Fin.addCases (Fin.addCases b d) v))
        (M8.AtomOps.refine (Route.cols g))) t
    ext (Shared50RecursiveNodeRows.transpose (one_dvd _) x) (cell d h).val = ext x (cell h d).val := by
  intro cell
  rw [show (cell d h).val = _ from remainderPlacement_childAddress a b d h u v g t,
    show (cell h d).val = _ from remainderPlacement_childAddress a b h d u v g t,
    ext_apply,ext_apply]
  exact intervalAddress_transpose 64 x a b h d u v (finProdFinEquiv (LabelAddress.address g,t))

/-- Read the three contiguous slices of a field from its absolute digit
positions. Ranking the slices recovers the original field rank. -/
private theorem intervalSlices_rank {n lo hi M : ℕ} [NeZero M]
    (ordered : lo ≤ hi) (fits : hi ≤ n) (x : Fin n → ZMod M) :
    let a := fun i : Fin lo => x ⟨i.val,by omega⟩
    let h := fun i : Fin (hi-lo) => x ⟨lo+i.val,by omega⟩
    let u := fun i : Fin (n-hi) => x ⟨hi+i.val,by omega⟩
    (FlatCoordinateLayout.rank (Fin.addCases (Fin.addCases a h) u)).val =
      (FlatCoordinateLayout.rank x).val := by
  intro a h u
  have size : lo+(hi-lo)+(n-hi) = n := by omega
  have same : Fin.addCases (motive := fun _ => ZMod M) (Fin.addCases a h) u = x ∘ Fin.cast size := by
    funext j
    induction j using Fin.addCases with
    | left j =>
      induction j using Fin.addCases with
      | left j => simp only [Fin.addCases_left]; rfl
      | right j => simp only [Fin.addCases_right,Fin.addCases_left]; rfl
    | right j =>
      simp only [Fin.addCases_right,Function.comp_apply,u]
      congr 1
      apply Fin.ext
      simp only [Fin.val_cast,Fin.val_natAdd]
      omega
  rw [same]
  have castRank {m : ℕ} (e : m = n) : (FlatCoordinateLayout.rank (x ∘ Fin.cast e)).val = (FlatCoordinateLayout.rank x).val := by subst m; rfl
  exact castRank size

/-- The concrete child reads arbitrary full fields in absolute coordinates.
Only digits in the scheduled interval cross between the two fields. -/
theorem remainderPlacement_fullChildRead {lo hi w K : ℕ} (ordered : lo ≤ hi) (fits : hi ≤ 64)
    (x : Fin (volume prime (phaseIntervalChild lo hi w ((prime^w)^(64*64)*K) 64)) → ZMod 2)
    (h d : Fin 64 → ZMod (prime^w)) (g : LabelPadding.Label 64 w) (t : Fin K) :
    let swap := fun (a b : Fin 64 → ZMod (prime^w)) (i : Fin 64) =>
      if lo ≤ i.val ∧ i.val < hi then b i else a i
    let cell := fun (a b : Fin 64 → ZMod (prime^w)) => FlatCoordinateLayout.index
      (Fin.addCases (Fin.addCases a b) (M8.AtomOps.refine (Route.cols g))) t
    ext (Shared50RecursiveNodeRows.transpose (one_dvd _) x) (cell (swap h d) (swap d h)).val =
      ext x (cell h d).val := by
  intro swap cell
  let pre (a : Fin 64 → ZMod (prime^w)) (i : Fin lo) := a ⟨i.val,by omega⟩
  let active (a : Fin 64 → ZMod (prime^w)) (i : Fin (hi-lo)) := a ⟨lo+i.val,by omega⟩
  let tail (a : Fin 64 → ZMod (prime^w)) (i : Fin (64-hi)) := a ⟨hi+i.val,by omega⟩
  have pack (a : Fin 64 → ZMod (prime^w)) := intervalSlices_rank ordered fits a
  have crossed (a b : Fin 64 → ZMod (prime^w)) :
      (FlatCoordinateLayout.rank (Fin.addCases (Fin.addCases (pre a) (active b)) (tail a))).val =
        (FlatCoordinateLayout.rank (swap a b)).val := by
    have left : pre (swap a b) = pre a := by funext i; simp [pre,swap,show ¬ lo ≤ i.val by omega]
    have middle : active (swap a b) = active b := by
      funext i; simp [active,swap,show lo ≤ lo+i.val ∧ lo+i.val < hi by omega]
    have right : tail (swap a b) = tail a := by funext i; simp [tail,swap,show ¬ hi+i.val < hi by omega]
    have eq := pack (swap a b)
    change (FlatCoordinateLayout.rank (Fin.addCases (Fin.addCases (pre _) (active _)) (tail _))).val = _ at eq
    rwa [left,middle,right] at eq
  have read := remainderPlacement_childRead x (pre h) (pre d) (active h) (active d) (tail h) (tail d) g t
  have size : lo+(hi-lo)+(64-hi) = 64 := by omega
  have hh := pack h
  have dd := pack d
  change (FlatCoordinateLayout.rank (Fin.addCases (Fin.addCases (pre h) (active h)) (tail h))).val = _ at hh
  change (FlatCoordinateLayout.rank (Fin.addCases (Fin.addCases (pre d) (active d)) (tail d))).val = _ at dd
  have hd := crossed h d
  have dh := crossed d h
  simp only [ArbitraryWidthSliceTranspose.rank_append] at hh dd hd dh
  simpa only [cell,FlatCoordinateLayout.index_val,ArbitraryWidthSliceTranspose.rank_append,hh,dd,hd,dh,size] using read

/-- Follow an arbitrary packed atom vector through the physical digit swaps,
keeping the enclosing descriptor's prefix and suffix at the same addresses. -/
private theorem packedAtoms_read {n w B : ℕ} {v : Descriptor}
    (shape : v.beforeH = B*prime^(n*w)) (ps : List (LabelSchedule.Pair n)) {x y}
    (steps : LabelSchedule.Swaps v w B ps x y) :
    ∀ (a : Fin v.beforeRows) (r : Fin v.rows) (b : Fin B)
      (h d : Fin (prime^v.width)) (mid : Fin v.between) (j : Fin v.afterD)
      (digits : Fin n → ZMod (prime^w)),
      let cell := fun u : Fin n → ZMod (prime^w) => RecursiveInterchangeLayout.index prime v
        a r (b.val*prime^(n*w)+(FlatCoordinateLayout.rank u).val) h mid d j
      y (cell (digits ∘ (ps.map fun p => Equiv.swap p.val.1 p.val.2).prod)) = x (cell digits) := by
  induction ps generalizing x with
  | nil => subst y; intros; rfl
  | cons p ps ih =>
    obtain ⟨z,step,rest⟩ := steps
    intro a r b h d mid j digits cell
    let s := p.val.1
    let t := p.val.2
    have lt : s < t := p.property
    have update : digits ∘ Equiv.swap s t = Function.update (Function.update digits s (digits t)) t (digits s) := by
      funext i
      by_cases eq : i = s
      · subst i; simp [Function.update_of_ne lt.ne]
      by_cases eq' : i = t
      · subst i; simp
      simp [Function.comp_apply,Equiv.swap_apply_of_ne_of_ne eq eq',Function.update_of_ne eq,Function.update_of_ne eq']
    obtain ⟨pre,gap,last,old,new⟩ := LabelColumns.rank_pair_update digits s t lt (digits t) (digits s)
    have radix (k : ℕ) : (prime^w)^k = prime^(k*w) := by rw [← pow_mul,Nat.mul_comm]
    have read := LabelView.swap_cols shape lt t.isLt step a.isLt r.isLt b.isLt
      (by simpa only [radix] using pre.isLt) (ZMod.val_lt (digits t))
      (by simpa only [radix] using gap.isLt) (ZMod.val_lt (digits s))
      (by simpa only [radix] using last.isLt) h.isLt mid.isLt d.isLt j.isLt
    apply (ih rest a r b h d mid j (digits ∘ Equiv.swap s t)).trans
    change z (cell (digits ∘ Equiv.swap s t)) = x (cell digits)
    simpa only [cell,update,new,old,LabelView.label,Nat.mul_one,Nat.one_mul,radix] using read

/-- Packed reads when the external fields exchange places with the two chart rows. -/
def RemainderPlacementReads (v : Descriptor) (w B : ℕ) (x y : ℕ → ZMod 2) :=
  let n := 128+64*64
  let flat := (@finSumFinEquiv 128 (64*64)).symm
  ∀ (a : Fin v.beforeRows) (r : Fin v.rows) (b : Fin B)
  (h d : Fin (prime^v.width)) (mid : Fin v.between) (j : Fin v.afterD)
  (digits : Fin n → ZMod (prime^w)),
  let cell := fun u : Fin n → ZMod (prime^w) => RecursiveInterchangeLayout.index prime v
    a r (b.val*prime^(n*w)+(FlatCoordinateLayout.rank u).val) h mid d j
  y (cell (digits ∘ flat.trans (remainderRowPlacement.trans flat.symm))) = x (cell digits)

/-- Change only the matrix-label digits in a packed address. -/
def remainderChartDigits {w : ℕ} (f : LabelPadding.Label 64 w → LabelPadding.Label 64 w)
    (digits : Fin (128+64*64) → ZMod (prime^w)) : Fin (128+64*64) → ZMod (prime^w) :=
  let g : LabelPadding.Label 64 w := fun r i => digits (Fin.natAdd 128 (finProdFinEquiv (i,r)))
  Fin.addCases (fun i => digits (Fin.castAdd (64*64) i)) (M8.AtomOps.refine (Route.cols (f g)))

/-- The address reached by an entire placed chart, including both placements. -/
def placedChartDigits {w : ℕ} (f : LabelPadding.Label 64 w → LabelPadding.Label 64 w)
    (digits : Fin (128+64*64) → ZMod (prime^w)) :=
  let flat := (@finSumFinEquiv 128 (64*64)).symm
  let swap := flat.trans (remainderRowPlacement.trans flat.symm)
  remainderChartDigits f (digits ∘ swap) ∘ swap

private theorem remainderRowPlacement_row (r : Fin 2) (i : Fin 64) :
    remainderRowPlacement (.inr (finProdFinEquiv (i,Fin.castAdd 62 r))) =
      .inl (finProdFinEquiv (r,i)) := by
  change placeRemainderRow (.inr (finProdFinEquiv (i,Fin.castAdd 62 r))) = _
  simp [placeRemainderRow]

/-- Each exposed external field undergoes right multiplication by the chart,
independently of all label digits. -/
theorem placedChartDigits_field {w : ℕ} (H : LabelPadding.Label 64 w)
    (digits : Fin (128+64*64) → ZMod (prime^w)) (r : Fin 2) (i : Fin 64) :
    let field := fun (j : Fin 64) => Fin.castAdd (64*64) (finProdFinEquiv (r,j))
    placedChartDigits (fun g => g*H) digits (field i) =
      ∑ j, digits (field j)*H j i := by
  intro field
  simp only [placedChartDigits,Function.comp_apply,Equiv.trans_apply,field,
    finSumFinEquiv_symm_apply_castAdd,remainderRowPlacement_field,Equiv.symm_symm,
    finSumFinEquiv_apply_right,remainderChartDigits,Fin.addCases_right,M8.AtomOps.refine,
    Equiv.symm_apply_apply,Route.cols,finSumFinEquiv_symm_apply_natAdd]
  let A : Matrix (Fin 64) (Fin 64) (ZMod (prime^w)) := fun r i =>
    digits (finSumFinEquiv (remainderRowPlacement (.inr (finProdFinEquiv (i,r)))))
  change (A*H) (Fin.castAdd 62 r) i = _
  rw [Matrix.mul_apply]
  simp only [A,remainderRowPlacement_row,finSumFinEquiv_apply_left]

/-- Changing the external fields cannot affect a label digit after a placed
chart: rows zero and one are parked, and all other rows mix only within themselves. -/
theorem placedChartDigits_label_congr {w : ℕ} (H : LabelPadding.Label 64 w)
    {x y : Fin (128+64*64) → ZMod (prime^w)}
    (same : ∀ l, x (Fin.natAdd 128 l) = y (Fin.natAdd 128 l)) (l : Fin (64*64)) :
    placedChartDigits (fun g => g*H) x (Fin.natAdd 128 l) =
      placedChartDigits (fun g => g*H) y (Fin.natAdd 128 l) := by
  obtain ⟨⟨i,r⟩,rfl⟩ := (@finProdFinEquiv 64 64).surjective l
  induction r using Fin.addCases (m := 2) (n := 62) with
  | left r =>
    simpa only [placedChartDigits,Function.comp_apply,Equiv.trans_apply,Equiv.symm_symm,
      finSumFinEquiv_symm_apply_natAdd,remainderRowPlacement_row,finSumFinEquiv_apply_left,
      remainderChartDigits,Fin.addCases_left,finSumFinEquiv_symm_apply_castAdd,
      remainderRowPlacement_field,finSumFinEquiv_apply_right] using same (finProdFinEquiv (i,Fin.castAdd 62 r))
  | right r =>
    simp only [placedChartDigits,Function.comp_apply,Equiv.trans_apply,Equiv.symm_symm,
      finSumFinEquiv_symm_apply_natAdd,remainderRowPlacement_spectator,finSumFinEquiv_apply_right,
      remainderChartDigits,Fin.addCases_right,M8.AtomOps.refine,Equiv.symm_apply_apply,Route.cols]
    let A (z : Fin (128+64*64) → ZMod (prime^w)) : LabelPadding.Label 64 w := fun r i =>
      z (finSumFinEquiv (remainderRowPlacement (.inr (finProdFinEquiv (i,r)))))
    change (A x*H) (Fin.natAdd 2 r) i = (A y*H) (Fin.natAdd 2 r) i
    rw [Matrix.mul_apply,Matrix.mul_apply]
    simp only [A,remainderRowPlacement_spectator,finSumFinEquiv_apply_right,same]

theorem placedChartDigits_read {v : Descriptor} {w B : ℕ} {x p q y : ℕ → ZMod 2}
    {f : LabelPadding.Label 64 w → LabelPadding.Label 64 w}
    (place : RemainderPlacementReads v w B x p)
    (chart : LabelPermutation.Transport v (B*(prime^w)^128) w f p q)
    (returnRows : RemainderPlacementReads v w B q y)
    (a : Fin v.beforeRows) (r : Fin v.rows) (b : Fin B) (h d : Fin (prime^v.width))
    (mid : Fin v.between) (j : Fin v.afterD) (digits : Fin (128+64*64) → ZMod (prime^w)) :
    let cell := fun u : Fin (128+64*64) → ZMod (prime^w) => RecursiveInterchangeLayout.index prime v
      a r (b.val*prime^((128+64*64)*w)+(FlatCoordinateLayout.rank u).val) h mid d j
    y (cell (placedChartDigits f digits)) = x (cell digits) := by
  intro cell
  let flat := (@finSumFinEquiv 128 (64*64)).symm
  let placed := digits ∘ flat.trans (remainderRowPlacement.trans flat.symm)
  have move := returnRows a r b h d mid j (remainderChartDigits f placed)
  have run := remainderPlacement_chartRead chart a r b h d mid j placed
  exact move.trans (run.trans (place a r b h d mid j digits))

/-- Inverse chart passes cancel on every packed digit, including the external
fields and singular labels. -/
theorem placedChartDigits_inverse {w : ℕ} {f g : LabelPadding.Label 64 w → LabelPadding.Label 64 w}
    (undo : Function.LeftInverse g f) (digits : Fin (128+64*64) → ZMod (prime^w)) :
    placedChartDigits g (placedChartDigits f digits) = digits := by
  let flat := (@finSumFinEquiv 128 (64*64)).symm
  let swap := flat.trans (remainderRowPlacement.trans flat.symm)
  have twice (i) : swap (swap i) = i := by
    simp only [swap,Equiv.trans_apply,Equiv.apply_symm_apply]
    change flat.symm (remainderRowPlacement.symm (remainderRowPlacement (flat i))) = i
    simp
  have cancel (x : Fin (128+64*64) → ZMod (prime^w)) : (x ∘ swap) ∘ swap = x := by
    funext i
    simp only [Function.comp_apply,twice]
  have chartUndo (x : Fin (128+64*64) → ZMod (prime^w)) :
      remainderChartDigits g (remainderChartDigits f x) = x := by
    funext i
    induction i using Fin.addCases with
    | left i => simp [remainderChartDigits]
    | right i =>
      obtain ⟨⟨c,r⟩,rfl⟩ := (@finProdFinEquiv 64 64).surjective i
      simp only [remainderChartDigits,Fin.addCases_right,M8.AtomOps.refine,Equiv.symm_apply_apply,Route.cols]
      exact congrFun (congrFun (undo (fun r i => x (Fin.natAdd 128 (finProdFinEquiv (i,r))))) r) c
  change (remainderChartDigits g ((remainderChartDigits f (digits ∘ swap) ∘ swap) ∘ swap)) ∘ swap = digits
  rw [cancel,chartUndo,cancel]

/-- The inverse chart restores the original independent label even after a
child changes both external fields. No invertibility of that label is needed. -/
theorem placedRemainder_label_restored {w : ℕ} (H : LabelPadding.Label 64 w) (orth : H*Hᵀ = 1)
    (x mid : Fin (128+64*64) → ZMod (prime^w))
    (child : ∀ l, mid (Fin.natAdd 128 l) = placedChartDigits (fun g => g*H) x (Fin.natAdd 128 l))
    (l : Fin (64*64)) :
    placedChartDigits (fun g => g*Hᵀ) mid (Fin.natAdd 128 l) = x (Fin.natAdd 128 l) := by
  apply (placedChartDigits_label_congr Hᵀ child l).trans
  exact congrFun (placedChartDigits_inverse (f := fun g => g*H) (g := fun g => g*Hᵀ)
    (fun g => by change g*H*Hᵀ = g; rw [Matrix.mul_assoc,orth,Matrix.mul_one]) x) _

/-- Parent field digits in stage-axis order followed by an independent label. -/
def remainderParentDigits {w : ℕ} (x : IntegerMultBounds.Swap.Shear.State Axis (ZMod (prime^w)))
    (label : LabelPadding.Label 64 w) : Fin (128+64*64) → ZMod (prime^w) :=
  Fin.addCases (fun j => let p := (@finProdFinEquiv 2 64).symm j
                         (if p.1 = 0 then x.1 else x.2) (stageAxis.symm p.2))
    (M8.AtomOps.refine (Route.cols label))

private theorem placedParentField (c : PortCertificate) {w : ℕ}
    (x : IntegerMultBounds.Swap.Shear.State Axis (ZMod (prime^w))) (label : LabelPadding.Label 64 w)
    (r : Fin 2) (i : Fin 64) :
    let H := reduce (prime^w) (c.fullChart.submatrix stageAxis.symm remainderAxis)
    placedChartDigits (fun g => g*H) (remainderParentDigits x label)
        (Fin.castAdd (64*64) (finProdFinEquiv (r,i))) =
      ((reduce (prime^w) c.fullChart)ᵀ *ᵥ (if r = 0 then x.1 else x.2)) (remainderAxis i) := by
  intro H
  rw [placedChartDigits_field]
  let A : LabelPadding.Label 64 w := fun _ j => (if r = 0 then x.1 else x.2) (stageAxis.symm j)
  have row := remainderChart_row c w A 0 i
  rw [Matrix.mul_apply] at row
  simpa only [remainderParentDigits,Fin.addCases_left,Equiv.symm_apply_apply,A,H] using row

/-- If the child exchanges the two charted slices at a parent address and
preserves its label, the inverse chart returns exactly the parent port exchange. -/
theorem placedRemainder_parentDigits (c : PortCertificate) (hc : c.Checked) {lo hi w : ℕ}
    (fits : hi ≤ 63) (x : IntegerMultBounds.Swap.Shear.State Axis (ZMod (prime^w)))
    (label : LabelPadding.Label 64 w) (mid : Fin (128+64*64) → ZMod (prime^w)) :
    let H := reduce (prime^w) (c.fullChart.submatrix stageAxis.symm remainderAxis)
    let before := placedChartDigits (fun g => g*H) (remainderParentDigits x label)
    let field := fun (r : Fin 2) (i : Fin 64) => Fin.castAdd (64*64) (finProdFinEquiv (r,i))
    (∀ i, (mid (field 0 i), mid (field 1 i)) =
      if lo ≤ i.val ∧ i.val < hi then (before (field 1 i),before (field 0 i)) else
        (before (field 0 i),before (field 1 i))) →
    (∀ l, mid (Fin.natAdd 128 l) = before (Fin.natAdd 128 l)) →
    placedChartDigits (fun g => g*Hᵀ) mid =
      remainderParentDigits (M8.Exchange.exchange (reduce (prime^w) (c.span lo hi)) x) label := by
  intro H before field active spectator
  let y := M8.Exchange.exchange (reduce (prime^w) (c.span lo hi)) x
  have aligned : mid = placedChartDigits (fun g => g*H) (remainderParentDigits y label) := by
    funext j
    induction j using Fin.addCases with
    | left j =>
      obtain ⟨⟨r,i⟩,rfl⟩ := (@finProdFinEquiv 2 64).surjective j
      have pair := active i
      simp only [before,field,H,placedParentField,ite_true,one_ne_zero,ite_false] at pair
      have ys := pair.trans (remainderExchange_tapeDigits c hc lo hi w fits x i).symm
      fin_cases r
      · exact (congrArg Prod.fst ys).trans (by simpa [H,y] using (placedParentField c y label 0 i).symm)
      · exact (congrArg Prod.snd ys).trans (by simpa [H,y] using (placedParentField c y label 1 i).symm)
    | right l =>
      exact (spectator l).trans (placedChartDigits_label_congr H
        (x := remainderParentDigits x label) (y := remainderParentDigits y label)
        (fun i => by simp [remainderParentDigits]) l)
  rw [aligned]
  apply placedChartDigits_inverse
  intro g
  change g*H*Hᵀ = g
  rw [Matrix.mul_assoc,(remainderChart_reduced c hc w).2,Matrix.mul_one]

/-- Follow an arbitrary parent address through the actual interval child:
the same intermediate digits give its physical output read and the inverse
chart's parent exchange. -/
theorem placedRemainder_childEndpoint (c : PortCertificate) (hc : c.Checked) {lo hi w K : ℕ}
    (ordered : lo ≤ hi) (fits : hi ≤ 63)
    (word : Fin (volume prime (phaseIntervalChild lo hi w ((prime^w)^(64*64)*K) 64)) → ZMod 2)
    (x : IntegerMultBounds.Swap.Shear.State Axis (ZMod (prime^w)))
    (label : LabelPadding.Label 64 w) (t : Fin K) :
    let H := reduce (prime^w) (c.fullChart.submatrix stageAxis.symm remainderAxis)
    let before := placedChartDigits (fun g => g*H) (remainderParentDigits x label)
    ∃ mid, ext (Shared50RecursiveNodeRows.transpose (one_dvd _) word) (FlatCoordinateLayout.index mid t).val =
      ext word (FlatCoordinateLayout.index before t).val ∧
      placedChartDigits (fun g => g*Hᵀ) mid =
        remainderParentDigits (M8.Exchange.exchange (reduce (prime^w) (c.span lo hi)) x) label := by
  intro H before
  let h := fun i : Fin 64 => before (Fin.castAdd (64*64) (Fin.castAdd 64 i))
  let d := fun i : Fin 64 => before (Fin.castAdd (64*64) (Fin.natAdd 64 i))
  let g : LabelPadding.Label 64 w := fun r i => before (Fin.natAdd 128 (finProdFinEquiv (i,r)))
  let pack := fun (a b : Fin 64 → ZMod (prime^w)) =>
    Fin.addCases (motive := fun _ => ZMod (prime^w)) (Fin.addCases a b) (M8.AtomOps.refine (Route.cols g))
  have unpack : pack h d = before := by
    funext j
    induction j using Fin.addCases with
    | left j =>
      induction j using Fin.addCases (m := 64) (n := 64) with
      | left i => simp [pack,h]
      | right i => simp only [pack,Fin.addCases_left,Fin.addCases_right,d]
    | right j =>
      obtain ⟨⟨i,r⟩,rfl⟩ := (@finProdFinEquiv 64 64).surjective j
      simp [pack,M8.AtomOps.refine,Route.cols,g]
  let swap := fun (a b : Fin 64 → ZMod (prime^w)) (i : Fin 64) =>
    if lo ≤ i.val ∧ i.val < hi then b i else a i
  let mid := pack (swap h d) (swap d h)
  refine ⟨mid,?_,placedRemainder_parentDigits c hc fits x label mid ?_ ?_⟩
  · rw [← unpack]
    exact remainderPlacement_fullChildRead ordered (by omega) word h d g t
  · intro i
    have h0 : finProdFinEquiv ((0 : Fin 2),i) = Fin.castAdd 64 i := by
      apply Fin.ext; change i.val + 64*0 = i.val; omega
    have h1 : finProdFinEquiv ((1 : Fin 2),i) = Fin.natAdd 64 i := by
      apply Fin.ext; change i.val + 64*1 = 64+i.val; omega
    change (mid _,mid _) = ite _ (before _,before _) (before _,before _)
    by_cases live : lo ≤ i.val ∧ i.val < hi <;> simp only [h0,h1,live,mid,pack,swap,h,d,Fin.addCases_left,Fin.addCases_right,and_self,ite_true,ite_false]
  · intro l
    obtain ⟨⟨i,r⟩,rfl⟩ := (@finProdFinEquiv 64 64).surjective l
    simp only [mid,pack,Fin.addCases_right,M8.AtomOps.refine,Route.cols,Equiv.symm_apply_apply,g,before,H]

/-- A single physical schedule exchanges the external fields with the two
label rows at every precision. Its setup and all digit moves are absorbed
by the parent volume times the atom-width power. -/
theorem remainderRowPlacement_runs [M8.Machine.Net] {T : ℕ} (io : Fin T) :
    let n := 128+64*64
    let flat := (@finSumFinEquiv 128 (64*64)).symm
    ∃ ps : List (LabelSchedule.Pair n), ∃ C : ℝ,
      (ps.map fun p => Equiv.swap p.val.1 p.val.2).prod =
        flat.trans (remainderRowPlacement.trans flat.symm) ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
        v.beforeH = B*prime^(n*w) → v.Positive →
        ∀ (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2),
          roles.head io = 0 → roles.tape io = sourceWord x →
          ∃ (y : Fin (volume prime v) → ZMod 2) (t : ℕ), RemainderPlacementReads v w B (ext x) (ext y) ∧
            GraphContract.Runs (LabelSchedule.schedule io ps)
              (LabelCall.bank roles v (words (LabelSchedule.base v w)))
              (LabelCall.bank (setTape roles io (sourceWord y) 0) v (words (LabelSchedule.base v w))) t ∧
            (t : ℝ) ≤ C * volume prime v * (w : ℝ)^M8.Machine.BudgetBound.tau := by
  intro n flat
  obtain ⟨ps,route,_,run⟩ := LabelSchedule.permutation_schedule
    (flat.trans (remainderRowPlacement.trans flat.symm)) io
  let k := n-1
  let setup := LabelSchedule.countCost ps
  obtain ⟨C,bound⟩ := scaledRoute_cost_bound (setup+k*3808274) k 1 (by decide)
  refine ⟨ps,C,route.symm,?_⟩
  intro v w B hw hb shape pos roles x head word
  obtain ⟨y,steps,exec⟩ := run v w B hw hb shape pos roles x head word
  refine ⟨y,_,by unfold RemainderPlacementReads; dsimp only; rw [route]; exact packedAtoms_read shape ps steps,exec,le_trans ?_ (bound (volume prime v) w hw)⟩
  simp only [Nat.mul_one]
  exact_mod_cast (show setup+k*(3808274*volume prime v+LeafCore.coreCost (volume prime v) w) ≤ _ by
    rw [Nat.add_mul,Nat.mul_add,Nat.mul_assoc]
    have := Nat.le_mul_of_pos_right setup (RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v pos)
    omega)

/-- Place, chart, and expose the fields on the same owner tape. All three
blocks use the same descriptor registers, including for the inverse chart. -/
theorem placedRemainderChart_runs [M8.Machine.Net] {T : ℕ} (io : Fin T)
    (c : PortCertificate) (hc : c.Checked) (inverse : Bool) :
    let H := c.fullChart.submatrix stageAxis.symm remainderAxis
    let σ := if inverse then H.transpose else H
    ∃ block : Graph.Block (T+24) prime, ∃ C : ℝ, Blocks.Leading block ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
        v.beforeH = B*prime^((128+64*64)*w) → v.Positive →
        ∀ (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2),
          roles.head io = 0 → roles.tape io = sourceWord x →
          ∃ (placed charted y : Fin (volume prime v) → ZMod 2) (t : ℕ),
            RemainderPlacementReads v w B (ext x) (ext placed) ∧
            LabelPermutation.Transport v (B*(prime^w)^128) w (fun g => g*reduce (modulus w) σ)
              (ext placed) (ext charted) ∧ RemainderPlacementReads v w B (ext charted) (ext y) ∧
            GraphContract.Runs block (LabelCall.bank roles v (words (LabelSchedule.base v w)))
              (LabelCall.bank (setTape roles io (sourceWord y) 0) v (words (LabelSchedule.base v w))) t ∧
            (t : ℝ) ≤ C*volume prime v*(w : ℝ)^M8.Machine.BudgetBound.tau := by
  intro H σ
  obtain ⟨ps,P,_,place⟩ := remainderRowPlacement_runs io
  obtain ⟨chart,A,leading,run⟩ := remainderChart_runs io c hc inverse
  obtain ⟨Q,chartBound⟩ := scaledRoute_cost_bound A 63 64 (by decide)
  let swap := LabelSchedule.schedule io ps
  have lead := LabelSchedule.schedule_leading io ps
  refine ⟨Blocks.seqB (Blocks.seqB swap chart) swap,2*P+Q+2,Blocks.seq_leading _ _,?_⟩
  intro v w B hw hb shape pos roles x head word
  obtain ⟨placed,t,entry,enter,paid⟩ := place v w B hw hb shape pos roles x head word
  have chartShape : v.beforeH = B*(prime^w)^128*prime^(64*(w*64)) := by
    rw [shape,Nat.mul_assoc,← pow_mul,← pow_add]
    congr 2
    ring
  obtain ⟨charted,middle,act,_⟩ := run v w _ hw (Nat.mul_pos hb (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _))
    chartShape pos (setTape roles io (sourceWord placed) 0) placed (by simp [setTape]) (by simp [setTape])
  obtain ⟨y,u,exitRow,leave,last⟩ := place v w B hw hb shape pos
    (setTape roles io (sourceWord charted) 0) charted (by simp [setTape]) (by simp [setTape])
  simp only [SharedPlacementAlphabet.setTape_setTape] at act leave
  have first := Blocks.seq_runs lead leading enter act
  have both := Blocks.seq_runs (Blocks.seq_leading _ _) lead first leave
  refine ⟨placed,charted,y,_,entry,middle,exitRow,both,?_⟩
  have vol := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v pos
  have power := Real.one_le_rpow (show 1 ≤ (w : ℝ) by exact_mod_cast hw) M8.Machine.BudgetBound.exponent_range.1.le
  have one : 1 ≤ (volume prime v : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast vol) power
  have bill := chartBound (volume prime v) w hw
  push_cast at bill ⊢
  linarith only [paid,last,bill,one]

/-- The two placed charts sandwich one recursive call. The child's effect
and budget are carried through the composition on the same descriptor bank. -/
theorem placedRemainderChild_runs [M8.Machine.Net] {T : ℕ} (io : Fin T)
    (c : PortCertificate) (hc : c.Checked) (child : Graph.Block (T+24) prime)
    (childLeading : Blocks.Leading child) :
    let H := c.fullChart.submatrix stageAxis.symm remainderAxis
    ∃ block : Graph.Block (T+24) prime, ∃ C : ℝ, Blocks.Leading block ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
        v.beforeH = B*prime^((128+64*64)*w) → v.Positive →
        let Word := Fin (volume prime v) → ZMod 2
        let chartReads := fun σ (x y : Word) => ∃ p q : Word,
          RemainderPlacementReads v w B (ext x) (ext p) ∧
          LabelPermutation.Transport v (B*(prime^w)^128) w (fun g => g*reduce (modulus w) σ)
            (ext p) (ext q) ∧ RemainderPlacementReads v w B (ext q) (ext y)
        let bank := fun roles => LabelCall.bank roles v (words (LabelSchedule.base v w))
        ∀ (effect : Word → Word) (price : ℕ),
          (∀ (roles : Tapes T prime) (x : Word), roles.head io = 0 → roles.tape io = sourceWord x →
            GraphContract.Runs child (bank roles) (bank (setTape roles io (sourceWord (effect x)) 0)) price) →
          ∀ (roles : Tapes T prime) (x : Word), roles.head io = 0 → roles.tape io = sourceWord x →
            ∃ (z y : Word) (t : ℕ), chartReads H x z ∧ chartReads Hᵀ (effect z) y ∧
              GraphContract.Runs block (bank roles) (bank (setTape roles io (sourceWord y) 0)) t ∧
              (t : ℝ) ≤ C*volume prime v*(w : ℝ)^M8.Machine.BudgetBound.tau+price := by
  intro H
  obtain ⟨enter,P,enterLead,forward⟩ := placedRemainderChart_runs io c hc false
  obtain ⟨leave,Q,leaveLead,backward⟩ := placedRemainderChart_runs io c hc true
  refine ⟨Blocks.seqB (Blocks.seqB enter child) leave,P+Q+2,Blocks.seq_leading _ _,?_⟩
  intro v w B hw hb shape pos Word chartReads bank effect price call roles x head word
  obtain ⟨p,q,z,t,placed,charted,exposed,entry,paid⟩ := forward v w B hw hb shape pos roles x head word
  have step := call (setTape roles io (sourceWord z) 0) z (by simp [setTape]) (by simp [setTape])
  obtain ⟨p',q',y,u,restaged,uncharted,restored,exitRow,last⟩ := backward v w B hw hb shape pos
    (setTape roles io (sourceWord (effect z)) 0) (effect z) (by simp [setTape]) (by simp [setTape])
  simp only [SharedPlacementAlphabet.setTape_setTape] at step exitRow
  have first := Blocks.seq_runs enterLead childLeading entry step
  have both := Blocks.seq_runs (Blocks.seq_leading _ _) leaveLead first exitRow
  refine ⟨z,y,_,⟨p,q,placed,charted,exposed⟩,⟨p',q',restaged,uncharted,restored⟩,both,?_⟩
  have one : 1 ≤ (volume prime v : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast (RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v pos))
      (Real.one_le_rpow (by exact_mod_cast hw) M8.Machine.BudgetBound.exponent_range.1.le)
  push_cast
  linarith only [paid,last,one]

end

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
  obtain ⟨chart,undo⟩ := remainderChart_reduced c hc w
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
  have inv : H⁻¹ = Hᵀ := Matrix.inv_eq_right_inv undo
  rw [factor,Matrix.mul_inv_rev,inv]
  simp only [Matrix.mul_assoc]

/-- Every scheduled remainder has a nonidentity exchange at every positive atom
width. In the certificate chart the first digit of the interval witnesses it. -/
theorem remainderExchange_ne_one (c : PortCertificate) (hc : c.Checked)
    (e : ℕ × ℕ) (member : e ∈ BitHosting.remainderIntervals) (w : ℕ) :
    let M := prime^(w+1)
    let P := reduce M ((c.span e.1 e.2).submatrix stageAxis.symm stageAxis.symm)
    fromBlocks (1-P) P P (1-P) ≠ 1 := by
  intro M P same
  obtain ⟨active,fits,_⟩ := BitHosting.remainder_counts_strict e member
  let H := reduce M (c.fullChart.submatrix stageAxis.symm remainderAxis)
  have undo : Hᵀ*H = 1 := mul_eq_one_comm.mp (remainderChart_reduced c hc (w+1)).2
  have zero : P = 0 := by
    ext i j
    have entry := congrArg (fun A : Matrix (Fin 64 ⊕ Fin 64) (Fin 64 ⊕ Fin 64) (ZMod M) =>
      A (Sum.inl i) (Sum.inr j)) same
    simpa [Matrix.fromBlocks,Matrix.one_apply] using entry
  have routed := remainderProjector_atLabel c hc e.1 e.2 (w+1) fits Hᵀ
  change Hᵀ*P*(Hᵀ)⁻¹ = (Hᵀ*H)*_*(Hᵀ*H)⁻¹ at routed
  rw [zero,undo] at routed
  let a : Fin 64 := ⟨e.1,by omega⟩
  have entry := congrArg (fun A : Matrix (Fin 64) (Fin 64) (ZMod M) => A a a) routed
  have inside : e.1 ≤ a.val ∧ a.val < e.2 := ⟨le_rfl,active⟩
  haveI : Fact (1 < M) := ⟨one_lt_pow₀ (by exact Shared50ModularControl.prime_prime.one_lt) (by omega)⟩
  simpa [inside] using entry

/-- With the same injective chart at entry and exit, a single set bit
distinguishes the required exchange from retaining a singular row. -/
theorem remainderExchange_moved_bit {κ : Type*} (c : PortCertificate) (hc : c.Checked)
    (e : ℕ × ℕ) (member : e ∈ BitHosting.remainderIntervals) (w : ℕ) :
    let M := prime^(w+1)
    let P := reduce M ((c.span e.1 e.2).submatrix stageAxis.symm stageAxis.symm)
    ∀ chart : ((Fin 64 ⊕ Fin 64) → ZMod M) → κ, Function.Injective chart →
      ∃ (row : κ → ZMod 2) (x : (Fin 64 ⊕ Fin 64) → ZMod M), row (chart ((fromBlocks (1-P) P P (1-P)).mulVec x)) ≠
        row (chart x) := by
  classical
  intro M P chart inj
  have moved := remainderExchange_ne_one c hc e member w
  change fromBlocks (1-P) P P (1-P) ≠ 1 at moved
  rw [ne_eq,Matrix.ext_iff_mulVec] at moved
  push_neg at moved
  obtain ⟨x,hx⟩ := moved
  rw [Matrix.one_mulVec] at hx
  exact ⟨fun j => if j = chart x then 1 else 0,x,by simp [inj.ne hx]⟩

/-- A fixed interval swap cannot implement the routed projector at every live label.
Swap a digit inside the interval with the final digit, which lies outside every idle. -/
theorem remainderProjector_requires_label (c : PortCertificate) (hc : c.Checked)
    (lo hi : ℕ) (active : lo < hi) (fits : hi ≤ 63) :
    let P := reduce (prime^1) ((c.span lo hi).submatrix stageAxis.symm stageAxis.symm)
    let D : Matrix (Fin 64) (Fin 64) (ZMod (prime^1)) := diagonal fun i =>
      if lo ≤ i.val ∧ i.val < hi then 1 else 0
    ∃ g : LabelPadding.Label 64 1, IsUnit g ∧ g*P*g⁻¹ ≠ D := by
  intro P D
  let H := reduce (prime^1) (c.fullChart.submatrix stageAxis.symm remainderAxis)
  have undo : H*Hᵀ = 1 := (remainderChart_reduced c hc 1).2
  let a : Fin 64 := ⟨lo,by omega⟩
  let b : Fin 64 := 63
  let σ := Equiv.swap a b
  let S : LabelPadding.Label 64 1 := (1 : LabelPadding.Label 64 1).submatrix σ id
  let T : LabelPadding.Label 64 1 := (1 : LabelPadding.Label 64 1).submatrix id σ
  have st : S*T = 1 := by
    change (1 : LabelPadding.Label 64 1).submatrix σ (Equiv.refl _) * (1 : LabelPadding.Label 64 1).submatrix (Equiv.refl _) σ = _
    rw [submatrix_mul_equiv,Matrix.one_mul,submatrix_one_equiv]
  have su : IsUnit S := isUnit_iff_exists.mpr ⟨T,st,mul_eq_one_comm.mp st⟩
  refine ⟨S*Hᵀ,su.mul (isUnit_iff_exists.mpr ⟨H,mul_eq_one_comm.mp undo,undo⟩),?_⟩
  have routed : S*Hᵀ*H = S := by rw [Matrix.mul_assoc,mul_eq_one_comm.mp undo,Matrix.mul_one]
  rw [show S*Hᵀ*P*(S*Hᵀ)⁻¹ = (S*Hᵀ*H)*D*(S*Hᵀ*H)⁻¹ from
    remainderProjector_atLabel c hc lo hi 1 fits _,routed]
  intro eq
  have comm := congrArg (fun M : LabelPadding.Label 64 1 => M*S) eq
  change S*D*S⁻¹*S = D*S at comm
  rw [Matrix.mul_assoc,Matrix.inv_eq_right_inv st,mul_eq_one_comm.mp st,Matrix.mul_one] at comm
  have entry := congrArg (fun M : LabelPadding.Label 64 1 => M a b) comm
  change (S*D) a b = (D*S) a b at entry
  have ab : S a b = 1 := by simp [S,σ,Matrix.submatrix_apply,Matrix.one_apply]
  have outside : ¬ (lo ≤ b.val ∧ b.val < hi) := by change ¬ (lo ≤ 63 ∧ 63 < hi); omega
  simp only [D,Matrix.mul_diagonal,Matrix.diagonal_mul,ab,ite_eq_right outside,
    ite_eq_left (show lo ≤ a.val ∧ a.val < hi from ⟨le_rfl,active⟩),mul_zero,one_mul] at entry
  have pos : 1 < prime^1 := by simpa using Shared50ModularControl.prime_prime.one_lt
  letI : Fact (1 < prime^1) := ⟨pos⟩
  exact zero_ne_one entry

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

theorem intervalDiagonal_idem (m lo hi : ℕ) :
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

open IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal LabelCycle GoodForm in
open scoped Classical in
/-- Compute both idle dispatch tapes and the exceptional pivot schedules, with setup and
the excess branch work bounded on exactly the same physical directory. -/
theorem remainderDispatch_controls {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (lo hi : ℕ) (fits : hi ≤ 63) (rs : List (Pair T)) (hk : rs.length = 64*64)
    (α α' : Fin 64 → ZMod prime) (queue mask mode parents saved : Fin T)
    (apart : mask ≠ mode) (mq : mask ≠ queue) (bq : mode ≠ queue)
    (regs : ∀ j ∈ [queue,mask,mode], (parents :: saved :: (slots rs ++ [j])).Nodup) :
    let r := hi-lo
    let hr : r ≤ 64 := by dsimp [r]; omega
    let D : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if lo ≤ i.val ∧ i.val < hi then 1 else 0
    let table := Cover.Fallback.projectorResidual finSumFinEquiv (reduce prime D) α α'
    ∃ program : Pr P T Q A U, ∀ (v : Descriptor) (w B : ℕ),
      v.beforeH = B*prime^(64*((w+1)*64)) →
      ∀ (u : HS T Q A U) (S : Stacks T A), ready (prime^w) S.R rs → S.R saved = [] →
      (S.R parents).length = v.beforeRows*v.rows*B → S.R queue = [] → S.R mask = [] → S.R mode = [] →
      let labels := List.range (LabelMask.records v)
      let live := LabelStock.live 64 (w+1) 1
      let bad := fun j => Cover.Fallback.fallbackBit hr (reduce (prime^(w+1)) D)
        (Cover.Fallback.physicalLabel 64 (w+1) j)
      let codes := labels.flatMap fun j => if bad j then Cover.Fallback.residualSchedule (A := A)
        (table (LabelStock.residue 64 (w+1) 1 j)) else []
      ∃ z n, z.user = u.user ∧ n ≤ 3*((6+10*(64*64))*labels.length+4) ∧
        Exec body program (mk u S) n (mk z {S with R := (Function.update
          (Function.update (Function.update S.R queue codes) mask (labels.map fun j => bitSymbol (live j)))
          mode (labels.map fun j => bitSymbol (bad j)))}) ∧
        ∀ (goodCost padCost badCost : ℕ → ℕ) (base extra : ℕ),
          (∀ j ∈ labels, live j = true → bad j = false → goodCost j ≤ base) →
          (∀ j ∈ labels, live j = false → padCost j ≤ base) →
          (∀ j ∈ labels, live j = true → bad j = true → badCost j ≤ base+extra) →
          n + (labels.map fun j => (if live j then (if bad j then badCost j else goodCost j)
            else padCost j)+2+4).sum+2 ≤
            3*((6+10*(64*64))*labels.length+4) + labels.length*(base+6) +
            (((∑ k ∈ Finset.range r, (k+1)*65)*labels.length)/prime)*extra+2 := by
  intro r hr D table
  obtain ⟨program,write⟩ := Cover.Fallback.recordControls_exec body hr (reduce prime D) table rs hk
    queue mask mode parents saved apart mq bq regs
  refine ⟨program,?_⟩
  intro v w B shape u S radix scratch count freeQueue freeMask freeMode labels live bad codes
  have adm : Admissible prime D := by
    intro i j
    simp only [D,diagonal_apply]
    split_ifs <;> simp
  obtain ⟨z,n,user,time,run⟩ := write v w B _ (LabelProjector.residue_reduce (by omega : 0 < w+1) D adm)
    shape u S radix scratch count freeQueue freeMask freeMode
  refine ⟨z,n,user,time,run,?_⟩
  intro goodCost padCost badCost base extra hg hp hb
  have rank : D.rank = r := intervalDiagonal_rank (by omega : hi ≤ 64)
  obtain ⟨g,unit,good⟩ := LabelProjector.residue_witness (by omega : 0 < w+1) D
    (intervalDiagonal_idem 64 lo hi) (intervalFactor 64 lo hi) (intervalFactor_denominators 64 lo hi)
    (rank.trans_le hr)
  have bound := Cover.Fallback.directoryDispatchCost_le w r B hr (reduce (prime^(w+1)) D) v shape
    goodCost padCost badCost base extra g unit (by simpa only [rank] using good) hg hp hb
  simpa only [Nat.add_assoc] using Nat.add_le_add time bound

/-- At the scanner's physical directory index the archived matrix acts on the
incoming label's port projector. The chart transports liveness as well. -/
theorem remainderArchive_at (c : PortCertificate) (hc : c.Checked) (lo hi w : ℕ)
    (hw : 0 < w) (fits : hi ≤ 63) (block : ℕ)
    (g : LabelPadding.Label 64 w) (unit : IsUnit g) (α α' : Fin 64 → ZMod (prime^w)) :
    let H := reduce (prime^w) (c.fullChart.submatrix stageAxis.symm remainderAxis)
    let P := reduce (prime^w) ((c.span lo hi).submatrix stageAxis.symm stageAxis.symm)
    let D : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if lo ≤ i.val ∧ i.val < hi then 1 else 0
    let j := block*(prime^w)^(64*64)+(LabelAddress.address (g*H)).val
    LabelStock.live 64 w 1 j = true ∧
      Cover.Fallback.projectorResidual finSumFinEquiv (reduce (prime^w) D) α α'
        (Cover.Fallback.physicalLabel 64 w j) = Cover.Fallback.projectorResidual finSumFinEquiv P α α' g := by
  intro H P D j
  have routed : Cover.Fallback.physicalLabel 64 w j = g*H := by
    apply Eq.trans _ (Cover.Fallback.physicalLabel_address (g*H))
    simp [j,Cover.Fallback.physicalLabel,Nat.add_mod]
    rfl
  have undo : H*Hᵀ = 1 := (remainderChart_reduced c hc w).2
  refine ⟨(Cover.Fallback.physicalLabel_live hw j).mpr (routed ▸
    unit.mul (isUnit_iff_exists.mpr ⟨Hᵀ,undo,mul_eq_one_comm.mp undo⟩)),?_⟩
  have reduction : reduce (prime^w) D = diagonal (fun i : Fin 64 =>
      if lo ≤ i.val ∧ i.val < hi then (1 : ZMod (prime^w)) else 0) := by
    ext i j
    simp only [D,reduce, Matrix.map_apply,diagonal_apply]
    split_ifs <;> simp [ratMod_zero,ratMod_one]
  unfold Cover.Fallback.projectorResidual
  rw [routed,reduction,remainderProjector_atLabel c hc lo hi w fits g]

open M8.Exchange IntegerMultBounds.Swap.Shear in
/-- When the scanner selects its ordinary branch, the two triangular adapters
and the single weighted child implement the same incoming-label matrix as the archive. -/
theorem remainderOrdinary_address (c : PortCertificate) (hc : c.Checked) (lo hi w : ℕ)
    (hw : 0 < w) (fits : hi ≤ 63) (block : ℕ)
    (g : LabelPadding.Label 64 w) (unit : IsUnit g) (α α' : Fin 64 → ZMod (prime^w))
    (inverse : ∀ i, α i * α' i = 1) :
    let H := reduce (prime^w) (c.fullChart.submatrix stageAxis.symm remainderAxis)
    let P := reduce (prime^w) ((c.span lo hi).submatrix stageAxis.symm stageAxis.symm)
    let D : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if lo ≤ i.val ∧ i.val < hi then 1 else 0
    let j := block*(prime^w)^(64*64)+(LabelAddress.address (g*H)).val
    Cover.Fallback.fallbackBit D.rank_le_height (reduce (prime^w) D) (Cover.Fallback.physicalLabel 64 w j) = false →
    ∃ (L L' R R' K : LabelPadding.Label 64 w) (δ δ' : Fin 64 → ZMod (prime^w)),
      GoodForm.UnitLower L ∧ GoodForm.UnitLower L' ∧ GoodForm.UnitLower R ∧ GoodForm.UnitLower R' ∧
      (∀ i, δ i * δ' i = 1) ∧ ∀ x : Fin (64+64) → ZMod (prime^w),
        let e : (Fin 64 ⊕ Fin 64) ≃ Fin (64+64) := finSumFinEquiv
        let banks := (x ∘ e ∘ Sum.inl, x ∘ e ∘ Sum.inr)
        let result := transform (diagonal α * L * diagonal α') R'
          (cross (-K) (Weighted.child (hi-lo) (fun i => α i * δ i) (fun i => α' i * δ' i)
            (cross K (transform (diagonal α * L' * diagonal α') R banks))))
        (Cover.Fallback.projectorResidual finSumFinEquiv P α α' g).mulVec x =
          Sum.elim result.1 result.2 ∘ e.symm := by
  intro H P D j clear
  obtain ⟨live,archive⟩ := remainderArchive_at c hc lo hi w hw fits block g unit α α'
  change LabelStock.live 64 w 1 j = true at live
  change Cover.Fallback.projectorResidual finSumFinEquiv (reduce (prime^w) D) α α'
    (Cover.Fallback.physicalLabel 64 w j) = Cover.Fallback.projectorResidual finSumFinEquiv P α α' g at archive
  have good := Cover.Fallback.goodRecord_address hw finSumFinEquiv D (intervalDiagonal_idem 64 lo hi)
    (intervalFactor 64 lo hi) (intervalFactor_denominators 64 lo hi) D.rank_le_height j live clear α α' inverse
  simpa only [archive,show D.rank = hi-lo from intervalDiagonal_rank (by omega)] using good

/-- At a live routed record, the exceptional queue uses the reduction of the
incoming port's weighted residual, including the sign used by pivot recovery. -/
theorem remainderFallback_residual (c : PortCertificate) (hc : c.Checked) (lo hi w : ℕ)
    (hw : 0 < w) (fits : hi ≤ 63) (block : ℕ)
    (g : LabelPadding.Label 64 w) (unit : IsUnit g) (α α' : Fin 64 → ZMod (prime^w))
    (inv : ∀ i, α i * α' i = 1) :
    let H := reduce (prime^w) (c.fullChart.submatrix stageAxis.symm remainderAxis)
    let P := reduce (prime^w) ((c.span lo hi).submatrix stageAxis.symm stageAxis.symm)
    let D : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if lo ≤ i.val ∧ i.val < hi then 1 else 0
    let φ := LabelRing.res prime w hw
    let G := Cover.Fallback.projectorResidual finSumFinEquiv P α α' g
    let j := block*(prime^w)^(64*64)+(LabelAddress.address (g*H)).val
    (G.det = 1 ∨ G.det = -1) ∧ φ.mapMatrix G =
      Cover.Fallback.projectorResidual finSumFinEquiv (reduce prime D) (φ ∘ α) (φ ∘ α')
        (LabelStock.residue 64 w 1 j) := by
  intro H P D φ G j
  obtain ⟨live,same⟩ := remainderArchive_at c hc lo hi w hw fits block g unit α α'
  have adm : Admissible prime D := by
    intro i j
    simp only [D,diagonal_apply]
    split_ifs <;> simp
  have result := Cover.Fallback.physicalProjector_spec hw j live finSumFinEquiv D
    (intervalDiagonal_idem 64 lo hi) adm α α' inv
  change Cover.Fallback.projectorResidual finSumFinEquiv (reduce (prime^w) D) α α'
    (Cover.Fallback.physicalLabel 64 w j) = G at same
  rw [← same]
  exact result

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

/-- A scheduled chart uses a fixed machine and reads the layout from its headers.
Its output bank is ready for the same chart with the transformed payload. -/
structure RemainderChartFrame {k N : ℕ} (machine : SharedBankSkeleton.Skeleton k prime)
    (v : Descriptor) (w : ℕ) (stage : SharedBankStage.Stage _ k prime (phaseOwners (N := N))) : Prop where
  fixed : SharedBankSkeleton.ofStage stage = machine
  fits : k+24 ≤ stage.tapes
  leading : ∀ i, (stage.slots i).val = i.val
  input : ∀ data, stage.input data = SharedBankStageInput.raw
    (LabelCall.bank (phaseOwners data) v (words (LabelSchedule.base v w))) stage.tapes
  restored : ∀ data, stage.output data = stage.input (stage.transform data)

/-- A chart pass exposes the same permanent owner interface as the idle child,
even when its private tape count depends on the compiled block. -/
theorem remainderChart_stage [M8.Machine.Net] {k : ℕ} (src : Fin k) (c : PortCertificate)
    (hc : c.Checked) (inverse : Bool) :
    let H := c.fullChart.submatrix stageAxis.symm remainderAxis
    let σ := if inverse then H.transpose else H
    ∃ (C : ℕ) (machine : SharedBankSkeleton.Skeleton k prime), ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
      v.beforeH = B*prime^(64*(w*64)) → v.Positive →
      ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := volume prime v)),
        RemainderChartFrame machine v w stage ∧
        stage.cost = C*volume prime v + 63*LeafCore.coreCost (volume prime v) (w*64) ∧
        (∀ width : ℕ, w*64 ≤ width →
          ((stage.cost*(stage.tapes+5) : ℕ) : ℝ) ≤
            (((C : ℝ)+63*|LeafCore.C| * (width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime v)*(machine.tapes+5)) ∧
        ∀ data, (∀ j, j ≠ src → stage.transform data j = data j) ∧
          LabelPermutation.Transport v B w (fun g => g * reduce (modulus w) σ)
            (ext (data src)) (ext (stage.transform data src)) := by
  intro H σ
  obtain ⟨block,C,leading,runs⟩ := remainderChart_runs src c hc inverse
  let machine : SharedBankSkeleton.Skeleton k prime :=
    {block with slots := fun i => block.slots (Fin.castAdd 24 i),
                slots_injective := block.slots_injective.comp (Fin.castAdd_injective k 24)}
  refine ⟨C,machine,?_⟩
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
            strip_input := fun _ => routePrivate block leading _ _ v d, realizes := ?_ },⟨rfl,SharedBankFamily.common_le block,(fun i => leading (Fin.castAdd 24 i)),(fun _ => rfl),(fun _ => rfl)⟩,rfl,?_,?_⟩
  · intro data
    have run := (result data).choose_spec.2.1
    change GraphContract.Runs block _ (LabelCall.bank (setTape _ src (sourceWord (moved data)) 0) v d) _ at run
    rwa [updated] at run
  · intro width fits
    have bound := (result (fun _ _ => 0)).choose_spec.2.2 width fits
    push_cast at bound ⊢
    exact mul_le_mul_of_nonneg_right bound (by positivity)
  · intro data
    exact ⟨fun j off => Function.update_of_ne off .., by
      simpa only [transform,Function.update_self] using (result data).choose_spec.1⟩

/-- The placed chart shares the owner tapes with a child using its own header bank. -/
theorem placedRemainderChart_stage [M8.Machine.Net] {k : ℕ} (src : Fin k) (c : PortCertificate)
    (hc : c.Checked) (inverse : Bool) :
    let H := c.fullChart.submatrix stageAxis.symm remainderAxis
    let σ := if inverse then H.transpose else H
    ∃ (C : ℝ) (machine : SharedBankSkeleton.Skeleton k prime), ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
      v.beforeH = B*prime^((128+64*64)*w) → v.Positive →
      ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := volume prime v)),
        RemainderChartFrame machine v w stage ∧
        stage.cost = ⌈C*volume prime v*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊ ∧
        ∀ data, (∀ j, j ≠ src → stage.transform data j = data j) ∧
          ∃ p q : Fin (volume prime v) → ZMod 2, RemainderPlacementReads v w B (ext (data src)) (ext p) ∧
            LabelPermutation.Transport v (B*(prime^w)^128) w (fun g => g*reduce (modulus w) σ)
              (ext p) (ext q) ∧ RemainderPlacementReads v w B (ext q) (ext (stage.transform data src)) := by
  intro H σ
  obtain ⟨block,C,leading,runs⟩ := placedRemainderChart_runs src c hc inverse
  let machine : SharedBankSkeleton.Skeleton k prime :=
    {block with slots := fun i => block.slots (Fin.castAdd 24 i),
                slots_injective := block.slots_injective.comp (Fin.castAdd_injective k 24)}
  refine ⟨C,machine,?_⟩
  intro v w B hw hb shape positive
  let result := fun data : Fin k → Fin (volume prime v) → ZMod 2 =>
    runs v w B hw hb shape positive (phaseOwners data) (data src) rfl
      (sourceWord_cast (v := v) rfl (data src)).symm
  let moved := fun data => (result data).choose_spec.choose_spec.choose
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
            strip_input := fun _ => routePrivate block leading _ _ v d, realizes := ?_ },⟨rfl,SharedBankFamily.common_le block,(fun i => leading (Fin.castAdd 24 i)),(fun _ => rfl),(fun _ => rfl)⟩,rfl,?_⟩
  · intro data
    obtain ⟨t,_,_,_,act,paid⟩ := (result data).choose_spec.choose_spec.choose_spec
    change GraphContract.Runs block _ (LabelCall.bank (setTape _ src (sourceWord (moved data)) 0) v d) t at act
    rw [updated] at act
    exact Blocks.runs_mono act (by exact_mod_cast paid.trans (Nat.le_ceil _))
  · intro data
    obtain ⟨_,entry,chart,exitRow,_,_⟩ := (result data).choose_spec.choose_spec.choose_spec
    exact ⟨fun j off => Function.update_of_ne off ..,_,_,entry,chart,by simpa only [transform,moved,Function.update_self] using exitRow⟩

/-- The interval program acts on the same array through either volume index. -/
private theorem remainderOwner_cast [M8.Machine.Net] {k w W V : ℕ} (src : Fin k)
    (e : ℕ × ℕ) (he : e ∈ BitHosting.remainderIntervals) (hw : 0 < w) (hW : 0 < W)
    (size : volume prime (phaseIntervalChild e.1 e.2 w W 64) = V) :
    let child := phaseIntervalChild e.1 e.2 w W 64
    ∃ mid : SharedBankStage.Stage _ k prime (phaseOwners (N := V)),
      mid.cost = (2*(24*64+333)+250)*((prime^w)^128*W)+1+
        cost child (fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child i)) ∧
      ∀ data, mid.transform data = Function.update data src (fun j =>
        Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (fun i => data src (i.cast size)) (j.cast size.symm)) := by
  subst V
  exact remainderOwner_stage src e he hw hW

/-- Run both placed charts around the prepared interval transpose on a shared
owner word. Each stage retains its private registers across the two joins. -/
theorem placedRemainderInterval_stage [M8.Machine.Net] {k : ℕ} (src : Fin k)
    (c : PortCertificate) (hc : c.Checked) (e : ℕ × ℕ) (member : e ∈ BitHosting.remainderIntervals) :
    ∃ P Q : ℝ, ∀ w K : ℕ, 0 < w → 0 < K →
      let M := prime^w
      let W := M^(64*64)*K
      let v : Descriptor := ⟨1,1,prime^((128+64*64)*w),0,1,K⟩
      let child := phaseIntervalChild e.1 e.2 w W 64
      let V := volume prime v
      let bill := (2*(24*64+333)+250)*(M^128*W)+1+
        cost child (fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child i))
      ∃ size : volume prime child = V,
      ∃ entry back stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)),
        stage.cost = ⌈P*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊+bill+1+
          ⌈Q*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊+1 ∧
        (∀ (inverse : Bool) data, let chart := if inverse then back else entry
          let H := c.fullChart.submatrix stageAxis.symm remainderAxis
          (∀ j, j ≠ src → chart.transform data j = data j) ∧
          ∃ p q : Fin V → ZMod 2, RemainderPlacementReads v w 1 (ext (data src)) (ext p) ∧
            LabelPermutation.Transport v (1*M^128) w
              (fun g => g*reduce (modulus w) (if inverse then H.transpose else H)) (ext p) (ext q) ∧
            RemainderPlacementReads v w 1 (ext q) (ext (chart.transform data src))) ∧
        ∀ data, let z := entry.transform data
                let move := Shared50RecursiveNodeRows.transpose (one_dvd child.rows)
                  (fun j => z src (j.cast size))
                stage.transform data = back.transform (Function.update z src (fun j => move (j.cast size.symm))) := by
  obtain ⟨P,_,forward⟩ := placedRemainderChart_stage src c hc false
  obtain ⟨Q,_,backward⟩ := placedRemainderChart_stage src c hc true
  refine ⟨P,Q,?_⟩
  intro w K hw hK M W v child V bill
  have pos : v.Positive := ⟨Nat.zero_lt_one,Nat.zero_lt_one,pow_pos Shared50ModularControl.prime_prime.pos _,Nat.zero_lt_one,hK⟩
  have shape : v.beforeH = 1*prime^((128+64*64)*w) := (one_mul _).symm
  obtain ⟨entry,_,entryCost,enterReads⟩ := forward v w 1 hw (by decide) shape pos
  obtain ⟨back,_,backCost,backReads⟩ := backward v w 1 hw (by decide) shape pos
  obtain ⟨lo,hi,_⟩ := BitHosting.remainder_counts e member
  have size : volume prime child = V := by
    rw [show volume prime child = _ from intervalChild_volume lo (show e.2 ≤ 64 by omega) w W]
    simp only [V,v,volume,M,W,one_mul,pow_zero,mul_one,← Nat.mul_assoc,← pow_add,← pow_mul]
    congr 2 <;> ring
  obtain ⟨mid,midCost,action⟩ := remainderOwner_cast src e member hw
    (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hK) size
  refine ⟨size,entry,back,SharedBankStage.compose (SharedBankStage.compose entry mid) back,?_,?_,?_⟩
  · change entry.cost+mid.cost+1+back.cost+1 = _
    rw [entryCost,midCost,backCost]
  · intro inverse data
    cases inverse
    · exact enterReads data
    · exact backReads data
  · intro data
    exact congrArg back.transform (action (entry.transform data))

section
local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩

private theorem oneBlockChart_read {w K : ℕ} {x p q y : ℕ → ZMod 2}
    {f : LabelPadding.Label 64 w → LabelPadding.Label 64 w} :
    let v : Descriptor := ⟨1,1,prime^((128+64*64)*w),0,1,K⟩
    RemainderPlacementReads v w 1 x p →
    LabelPermutation.Transport v (1*(prime^w)^128) w f p q → RemainderPlacementReads v w 1 q y →
    ∀ digits (t : Fin K), y (FlatCoordinateLayout.index (placedChartDigits f digits) t).val =
      x (FlatCoordinateLayout.index digits t).val := by
  intro v enter act leave digits t
  let zero : Fin (prime^v.width) := ⟨0,pow_pos Shared50ModularControl.prime_prime.pos _⟩
  have read := placedChartDigits_read enter act leave (a := (0 : Fin 1)) (r := (0 : Fin 1)) 0
    zero zero (0 : Fin 1) t digits
  let cell := fun u : Fin (128+64*64) → ZMod (prime^w) => RecursiveInterchangeLayout.index prime v
    0 0 (0*prime^((128+64*64)*w)+(FlatCoordinateLayout.rank u).val) 0 0 0 t
  have eq u : cell u = (FlatCoordinateLayout.index u t).val := by
    simp [cell,v,RecursiveInterchangeLayout.index,FlatCoordinateLayout.index_val]
  change y (cell (placedChartDigits f digits)) = x (cell digits) at read
  rwa [eq,eq] at read

/-- The composed one-block stage implements the parent exchange on the selected
owner and preserves every other owner, for all matrix labels and trailing cells. -/
theorem placedRemainder_parent_stage [M8.Machine.Net] {k : ℕ} (src : Fin k)
    (c : PortCertificate) (hc : c.Checked) (e : ℕ × ℕ) (member : e ∈ BitHosting.remainderIntervals) :
    ∃ P Q : ℝ, ∀ w K : ℕ, 0 < w → 0 < K →
      let M := prime^w
      let W := M^(64*64)*K
      let v : Descriptor := ⟨1,1,prime^((128+64*64)*w),0,1,K⟩
      let child := phaseIntervalChild e.1 e.2 w W 64
      let V := volume prime v
      ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)),
        stage.cost = ⌈P*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊+
          ((2*(24*64+333)+250)*(M^128*W)+1+
          cost child (fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child i)))+1+
          ⌈Q*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊+1 ∧
        ∀ data, (∀ j, j ≠ src → stage.transform data j = data j) ∧
          ∀ (x : IntegerMultBounds.Swap.Shear.State Axis (ZMod M)) (label : LabelPadding.Label 64 w) (t : Fin K),
          let y := M8.Exchange.exchange (reduce M (c.span e.1 e.2)) x
          ext (stage.transform data src) (FlatCoordinateLayout.index (remainderParentDigits y label) t).val =
            ext (data src) (FlatCoordinateLayout.index (remainderParentDigits x label) t).val := by
  obtain ⟨P,Q,build⟩ := placedRemainderInterval_stage src c hc e member
  refine ⟨P,Q,?_⟩
  intro w K hw hK M W v child V
  obtain ⟨size,entry,back,stage,bill,charts,result⟩ := build w K hw hK
  refine ⟨stage,bill,?_⟩
  intro data
  let z := entry.transform data
  let word := fun j => z src (Fin.cast size j)
  let move := Shared50RecursiveNodeRows.transpose (one_dvd child.rows) word
  let updated := Function.update z src (fun j => move (Fin.cast size.symm j))
  obtain ⟨off,p,q,place,forward,expose⟩ := charts false data
  obtain ⟨keep,p',q',unplace,inverse,restore⟩ := charts true updated
  rw [result data]
  change (∀ j, j ≠ src → back.transform updated j = data j) ∧ _
  refine ⟨fun j hj => (keep j hj).trans ((Function.update_of_ne hj ..).trans (off j hj)),?_⟩
  intro x label t y
  obtain ⟨lo,hi,_⟩ := BitHosting.remainder_counts e member
  obtain ⟨mid,read,parent⟩ := placedRemainder_childEndpoint c hc lo hi word x label t
  have first := oneBlockChart_read place forward expose (remainderParentDigits x label) t
  have last := oneBlockChart_read unplace inverse restore mid t
  let H := reduce M (c.fullChart.submatrix stageAxis.symm remainderAxis)
  let before := placedChartDigits (fun g => g*H) (remainderParentDigits x label)
  change placedChartDigits (fun g => g*Hᵀ) mid = remainderParentDigits y label at parent
  change ext (back.transform updated src) (FlatCoordinateLayout.index (placedChartDigits (fun g => g*Hᵀ) mid) t).val =
    ext (updated src) (FlatCoordinateLayout.index mid t).val at last
  rw [parent] at last
  simp only [updated,Function.update_self,ext_cast] at last
  change ext move (FlatCoordinateLayout.index mid t).val = ext word (FlatCoordinateLayout.index before t).val at read
  change ext (z src) (FlatCoordinateLayout.index before t).val = _ at first
  rw [show ext word = ext (z src) from ext_cast size _] at read
  exact last.trans (read.trans first)

end

/-- In inherited order the block index lies between the external fields and
the label. To exchange one digit across it, include that index in the middle
register of an ordinary equal-width transpose. -/
noncomputable def inheritedRowSwap (w B K : ℕ) (s : Fin 128) (l : Fin (64*64)) : Descriptor :=
  let M := prime^w
  ⟨1,1,M^s.val,w,(M^(127-s.val)*B)*M^l.val,M^(4095-l.val)*K⟩

theorem inheritedRowSwap_volume (w B K : ℕ) (s : Fin 128) (l : Fin (64*64)) :
    volume prime (inheritedRowSwap w B K s l) =
      (prime^w)^128*B*(prime^w)^(64*64)*K := by
  let M := prime^w
  change 1*1*M^s.val*M*((M^(127-s.val)*B)*M^l.val)*M*(M^(4095-l.val)*K) = _
  have split {n : ℕ} (i : Fin (n+1)) : M^i.val*M*M^(n-i.val) = M^(n+1) := by
    rw [← pow_succ,← pow_add]
    congr 1
    omega
  calc
    _ = (M^s.val*M*M^(127-s.val))*B*(M^l.val*M*M^(4095-l.val))*K := by ring
    _ = _ := by rw [split s,split l]

/-- Exact offset of the crossing transpose. Prefixes and suffixes are the
radix pieces around each selected digit in its original word. -/
theorem inheritedRowSwap_read {w B K : ℕ} (s : Fin 128) (l : Fin (64*64)) :
    let M := prime^w
    let v := inheritedRowSwap w B K s l
    ∀ (word : Fin (volume prime v) → ZMod 2) (p : Fin (M^s.val)) (h d : Fin M)
      (u : Fin (M^(127-s.val))) (b : Fin B) (q : Fin (M^l.val))
      (v' : Fin (M^(4095-l.val))) (t : Fin K),
      let cell := fun (h d : Fin M) =>
        ((((((p.val*M+h.val)*M^(127-s.val)+u.val)*B+b.val)*M^l.val+q.val)*M+d.val)*
          M^(4095-l.val)+v'.val)*K+t.val
      ext (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) word) (cell d h) =
        ext word (cell h d) := by
  intro M v word p h d u b q v' t cell
  let addr : RecursiveInterchangeScaling.Address v :=
    ⟨(0 : Fin 1),(0 : Fin 1),p,h,finProdFinEquiv (finProdFinEquiv (u,b),q),d,finProdFinEquiv (v',t)⟩
  have atCell (h d : Fin M) :
      (RecursiveInterchangeScaling.index ({addr with h := h, d := d} : RecursiveInterchangeScaling.Address v)).val =
        cell h d := by
    simp only [RecursiveInterchangeScaling.index_val,RecursiveInterchangeLayout.index,addr,cell,v,inheritedRowSwap,
      Fin.val_zero,Nat.zero_mul,Nat.zero_add,finProdFinEquiv_apply_val,M]
    ring
  rw [← atCell d h,← atCell h d,ext_apply,ext_apply]
  exact Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) (one_dvd _) word addr

section
open FlatCoordinateLayout
local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩

private theorem rank_update_parts {n M : ℕ} [NeZero M] (x : Fin n → ZMod M) (i : Fin n) :
    ∃ p : Fin (M^i.val), ∃ u : Fin (M^suffixFields i), ∀ z : ZMod M,
      (rank (Function.update x i z)).val = (p.val*M+z.val)*M^suffixFields i+u.val := by
  refine ⟨⟨_,prefix_lt x i⟩,⟨(rank x).val%M^suffixFields i,Nat.mod_lt _ (pow_pos (NeZero.pos M) _)⟩,?_⟩
  intro z
  have h := index_update x i z (0 : Fin 1)
  simpa only [index_val,suffixSize,suffix,Nat.mul_one,Fin.val_zero,Nat.add_zero,Nat.add_mul,Nat.mul_assoc] using h

/-- Address a parent bit in inherited order, with the independent block
between the field digits and the label digits. -/
noncomputable def inheritedDigitCell {w B K : ℕ} (x : Fin 128 ⊕ Fin (64*64) → ZMod (prime^w))
    (b : Fin B) (t : Fin K) : ℕ :=
  (((rank (x ∘ Sum.inl)).val*B+b.val)*(prime^w)^(64*64)+(rank (x ∘ Sum.inr)).val)*K+t.val

theorem inheritedRowSwap_digits {w B K : ℕ} (s : Fin 128) (l : Fin (64*64))
    (word : Fin (volume prime (inheritedRowSwap w B K s l)) → ZMod 2)
    (x : Fin 128 ⊕ Fin (64*64) → ZMod (prime^w)) (b : Fin B) (t : Fin K) :
    ext (Shared50RecursiveNodeRows.transpose (one_dvd _) word)
      (inheritedDigitCell (x ∘ Equiv.swap (.inl s) (.inr l)) b t) =
      ext word (inheritedDigitCell x b t) := by
  let M := prime^w
  obtain ⟨p,u,field⟩ := rank_update_parts (x ∘ Sum.inl) s
  obtain ⟨q,v,label⟩ := rank_update_parts (x ∘ Sum.inr) l
  have fields : (x ∘ Equiv.swap (.inl s) (.inr l)) ∘ Sum.inl =
      Function.update (x ∘ Sum.inl) s (x (.inr l)) := by
    funext j
    by_cases eq : j = s <;> simp [eq,Equiv.swap_apply_def]
  have labels : (x ∘ Equiv.swap (.inl s) (.inr l)) ∘ Sum.inr =
      Function.update (x ∘ Sum.inr) l (x (.inl s)) := by
    funext j
    by_cases eq : j = l <;> simp [eq,Equiv.swap_apply_def]
  have oldF := field (x (.inl s))
  have oldL := label (x (.inr l))
  rw [show x (.inl s) = (x ∘ Sum.inl) s from rfl,Function.update_eq_self] at oldF
  rw [show x (.inr l) = (x ∘ Sum.inr) l from rfl,Function.update_eq_self] at oldL
  have size : M^(64*64) = M^l.val*M*M^(4095-l.val) := by
    rw [← pow_succ,← pow_add]
    apply congrArg (M^·)
    have bound : l.val < 4096 := l.isLt
    omega
  have read := inheritedRowSwap_read s l word p ⟨_,ZMod.val_lt (x (.inl s))⟩
    ⟨_,ZMod.val_lt (x (.inr l))⟩ u b q v t
  unfold inheritedDigitCell
  rw [fields,labels,field,label,oldF,oldL]
  simp only [Function.comp_apply,suffixFields,← show M = prime^w from rfl,size] at read ⊢
  convert read using 2 <;> ring

end

/-- Column-major label digit paired with an external field digit. -/
def inheritedLabelDigit (s : Fin 128) : Fin (64*64) :=
  let p := (@finProdFinEquiv 2 64).symm s
  finProdFinEquiv (p.2,Fin.castAdd 62 p.1)

private theorem inheritedLabelDigit_injective : Function.Injective inheritedLabelDigit := by
  intro s t eq
  obtain ⟨⟨r,i⟩,rfl⟩ := (@finProdFinEquiv 2 64).surjective s
  obtain ⟨⟨u,j⟩,rfl⟩ := (@finProdFinEquiv 2 64).surjective t
  simp [inheritedLabelDigit] at eq
  exact congrArg finProdFinEquiv (Prod.ext ((Fin.castAdd_injective 2 62 eq.2)) eq.1)

/-- The 128 disjoint digit crossings implement the full placement. No crossing
involves a digit of the inherited block. -/
theorem inheritedRowSwap_schedule :
    let step := fun (i : Fin 128) => Equiv.swap (Sum.inl i) (Sum.inr (inheritedLabelDigit i))
    ∀ j, (List.finRange 128).foldl (fun a i => step i a) j = remainderRowPlacement j := by
  intro step
  have fixed (xs : List (Fin 128)) (j : Fin 128 ⊕ Fin (64*64))
      (left : ∀ i ∈ xs, j ≠ Sum.inl i) (right : ∀ i ∈ xs, j ≠ Sum.inr (inheritedLabelDigit i)) :
      xs.foldl (fun a i => step i a) j = j := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      rw [List.foldl_cons,show step i j = j from Equiv.swap_apply_of_ne_of_ne (left i (by simp)) (right i (by simp))]
      exact ih (fun t ht => left t (by simp [ht])) (fun t ht => right t (by simp [ht]))
  have pair (xs : List (Fin 128)) (nd : xs.Nodup) (s : Fin 128) (mem : s ∈ xs) :
      let run := xs.foldl (fun a i => step i a)
      run (Sum.inl s) = Sum.inr (inheritedLabelDigit s) ∧ run (Sum.inr (inheritedLabelDigit s)) = Sum.inl s := by
    induction xs with
    | nil => simp at mem
    | cons i xs ih =>
      obtain ⟨fresh,nd⟩ := List.nodup_cons.mp nd
      by_cases eq : s = i
      · subst s
        simp only [List.foldl_cons,step,Equiv.swap_apply_left,Equiv.swap_apply_right]
        constructor
        · exact fixed xs _ (by simp) (fun j hj eq => fresh (inheritedLabelDigit_injective (Sum.inr.inj eq) ▸ hj))
        · exact fixed xs _ (fun j hj eq => fresh (Sum.inl.inj eq ▸ hj)) (by simp)
      · have ne := inheritedLabelDigit_injective.ne eq
        simpa [List.foldl_cons,step,Equiv.swap_apply_def,eq,ne] using ih nd ((List.mem_cons.mp mem).resolve_left eq)
  intro j
  cases j with
  | inl s =>
    exact (pair _ (List.nodup_finRange _) s (List.mem_finRange s)).1
  | inr l =>
    obtain ⟨⟨i,r⟩,rfl⟩ := (@finProdFinEquiv 64 64).surjective l
    induction r using Fin.addCases (m := 2) (n := 62) with
    | left r =>
      let s := finProdFinEquiv (r,i)
      have eq : inheritedLabelDigit s = finProdFinEquiv (i,Fin.castAdd 62 r) := by simp [inheritedLabelDigit,s]
      rw [remainderRowPlacement_row,← eq]
      exact (pair _ (List.nodup_finRange _) s (List.mem_finRange s)).2
    | right r =>
      rw [remainderRowPlacement_spectator]
      apply fixed _ _ (by simp)
      intro s _ eq
      obtain ⟨⟨u,j⟩,rfl⟩ := (@finProdFinEquiv 2 64).surjective s
      have bad := congrArg Prod.snd (finProdFinEquiv.injective (Sum.inr.inj eq))
      simp only [inheritedLabelDigit,Equiv.symm_apply_apply] at bad
      have := congrArg Fin.val bad
      simp only [Fin.val_natAdd,Fin.val_castAdd] at this
      omega

/-- With their six descriptor headers supplied, the 128 crossings have one
uniform atom-width cost bound, including one sequencing step per crossing. -/
theorem inheritedRowSwap_cost [M8.Machine.Net] :
    ∃ C : ℝ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
      let V := (prime^w)^128*B*(prime^w)^(64*64)*K
      let view := fun s => inheritedRowSwap w B K s (inheritedLabelDigit s)
      ((∑ s : Fin 128, (cost (view s) (M8.RevMachine.Routines.hdr (view s))+1) : ℕ) : ℝ) ≤
        C*V*(w : ℝ)^M8.Machine.BudgetBound.tau := by
  obtain ⟨C,bound⟩ := scaledRoute_cost_bound 128 128 1 (by decide)
  refine ⟨C,?_⟩
  intro w B K hw hb hk V view
  have positive (s) : (view s).Positive :=
    ⟨Nat.zero_lt_one,Nat.zero_lt_one,pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _,
      Nat.mul_pos (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hb)
        (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _),
      Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hk⟩
  have each (s) : cost (view s) (M8.RevMachine.Routines.hdr (view s)) ≤ LeafCore.coreCost V w := by
    simpa only [view,inheritedRowSwap_volume,V,show (inheritedRowSwap w B K s (inheritedLabelDigit s)).width = w from rfl] using LeafCore.cost_le (positive s)
  have total := Finset.sum_le_sum (s := Finset.univ) (fun s _ => Nat.add_le_add_right (each s) 1)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at total
  have hv : 0 < V := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hb) (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)) hk
  apply le_trans ?_ (bound V w hw)
  have paid := total.trans (show 128*(LeafCore.coreCost V w+1) ≤ 128*V+128*LeafCore.coreCost V (w*1) by rw [Nat.mul_one]; omega)
  exact_mod_cast paid

/-- Construct the six inherited crossing headers from two copies of the atom
width and the independent trailing and block lengths. -/
theorem inheritedRowSwap_headers (s : Fin 128) (l : Fin (64*64)) :
    let outer := phaseField s.val (4095-l.val)
    let middle := phaseField 0 (127-s.val+l.val)
    let setup := FamilyPlacementAlphabet.sequence (FlatCoordinateDimensions.program outer)
      (FlatCoordinateDimensions.program middle)
    let slots : Fin 6 → Fin 18 := ![14,14,5,2,16,7]
    ∀ w B K, 0 < B → 0 < K →
      let M := prime^w
      let V := M^128*B*M^(64*64)*K
      let start := (FlatCoordinateDimensions.input w K).append (FlatCoordinateDimensions.input w B)
      let ready := (FlatCoordinateDimensions.output outer w K).append (FlatCoordinateDimensions.output middle w B)
      let headers := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (inheritedRowSwap w B K s l) i)
      HoareTime setup (fun z => z = start) (fun z => z = ready) ((2*(24*4224+333)+1)*V) ∧
      RecursiveDimensionBank.Headers (inheritedRowSwap w B K s l) headers ∧
      ∀ i, ready.head (slots i) = 1 ∧ ready.tape (slots i) = RadixZeroFill.encodedBinary (headers i) := by
  intro outer middle setup slots w B K hb hk M V start ready headers
  have suffix (a b : ℕ) : FlatCoordinateLayout.suffixFields (phaseField a b) = b := by
    unfold FlatCoordinateLayout.suffixFields phaseField
    simp only
    omega
  have hp : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have volume : V = M^4224*(B*K) := by
    dsimp only [V]
    rw [show (4224 : ℕ) = 128+64*64 by decide,pow_add]
    ring
  have big : 0 < V := by rw [volume]; exact Nat.mul_pos (pow_pos hp _) (Nat.mul_pos hb hk)
  have outerV : M^(s.val+1+(4095-l.val))*K ≤ V := by
    rw [volume]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right hp (by omega)) (Nat.le_mul_of_pos_left K hb)
  have middleV : M^(0+1+(127-s.val+l.val))*B ≤ V := by
    rw [volume]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right hp (by have := l.isLt; change l.val < 4096 at this; omega))
      (Nat.le_mul_of_pos_right B hk)
  have run := FamilyPlacementAlphabet.sequence_hoare (FlatCoordinateDimensions.construct_hoare outer w K hk)
    (FlatCoordinateDimensions.construct_hoare middle w B hb)
  refine ⟨run.consequence (fun _ h => h) (fun _ h => h) ?_,
    ⟨fun _ => FlatCoordinateSchedule.bits_value _,fun _ => FlatCoordinateSchedule.bits_canonical _⟩,?_⟩
  · have first := Nat.mul_le_mul (show 24*s.val+24*(4095-l.val)+333 ≤ 24*4224+333 by omega) outerV
    have second := Nat.mul_le_mul (show 24*0+24*(127-s.val+l.val)+333 ≤ 24*4224+333 by
      have := l.isLt; change l.val < 4096 at this; omega) middleV
    simp only [outer,middle,suffix,phaseField,ActualAffineScaling.modulus,M] at *
    omega
  · obtain ⟨_,pre,tail⟩ := FlatCoordinateDimensions.output_descriptors outer w K
    obtain ⟨_,one,gap⟩ := FlatCoordinateDimensions.output_descriptors middle w B
    have width := (FlatCoordinateDimensions.inputs_preserved outer w K).2.1
    have gapSize : M^(127-s.val+l.val)*B = (M^(127-s.val)*B)*M^l.val := by rw [pow_add]; ring
    have os : FlatCoordinateLayout.suffixFields outer = 4095-l.val := suffix _ _
    have ms : FlatCoordinateLayout.suffixFields middle = 127-s.val+l.val := suffix _ _
    simp only [FlatCoordinateLayout.prefixSize,FlatCoordinateLayout.suffixSize,os,ms,ActualAffineScaling.modulus] at pre tail one gap
    simp only [
      outer,middle,phaseField,ActualAffineScaling.modulus,pow_zero] at pre tail one gap
    rw [show prime^w = M from rfl,gapSize] at gap
    intro i
    fin_cases i <;> constructor <;> first | rfl | exact pre | exact tail | exact one | exact gap | exact width

/-- Build the crossing headers and immediately exchange the two digits on
the caller's owner. The private header bank is disjoint from every owner. -/
theorem inheritedRowSwap_runs [M8.Machine.Net] {n w B K : ℕ} (s : Fin 128) (l : Fin (64*64))
    (hb : 0 < B) (hk : 0 < K) (caller : Tapes n prime) (src : Fin n) :
    let outer := phaseField s.val (4095-l.val)
    let middle := phaseField 0 (127-s.val+l.val)
    let setup := FamilyPlacementAlphabet.sequence (FlatCoordinateDimensions.program outer)
      (FlatCoordinateDimensions.program middle)
    let slots : Fin 6 → Fin 18 := ![14,14,5,2,16,7]
    let headers := fun i => Fin.castAdd n (slots i)
    let site := Fin.natAdd 18 src
    let start := (FlatCoordinateDimensions.input w K).append (FlatCoordinateDimensions.input w B)
    let ready := (FlatCoordinateDimensions.output outer w K).append (FlatCoordinateDimensions.output middle w B)
    let v := inheritedRowSwap w B K s l
    ∀ x : Fin (volume prime v) → ZMod 2, caller.tape src = sourceWord x → caller.head src = 0 →
      HoareTime (seq (M8.Machine.ArbitraryWidthOriginalRun.extendBanks
          (extend (extend (extend setup n) 16) 19)) (program headers site))
        (fun z => z = input (start.append caller))
        (fun z => z = input (ready.append (setTape caller src
          (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) 0)))
        ((2*(24*4224+333)+1)*(volume prime v)+1+cost v (Routines.hdr v)) := by
  intro outer middle setup slots headers site start ready v x payload head
  obtain ⟨build,valid,ports⟩ := inheritedRowSwap_headers s l w B K hb hk
  have hp := pow_pos Shared50ModularControl.prime_prime.pos w
  have pos : v.Positive := ⟨Nat.zero_lt_one,Nat.zero_lt_one,pow_pos hp _,
    Nat.mul_pos (Nat.mul_pos (pow_pos hp _) hb) (pow_pos hp _),Nat.mul_pos (pow_pos hp _) hk⟩
  have act := M8.Machine.ArbitraryWidthOriginalTotalRun.runs (ready.append caller) headers site v
    (Routines.hdr v) pos valid
    (fun i => by simpa only [headers,ready,slots,outer,middle,v,Routines.hdr,Tapes.append,Fin.addCases_left] using (ports i).2)
    (fun i => by simpa only [headers,ready,slots,outer,middle,v,Routines.hdr,Tapes.append,Fin.addCases_left] using (ports i).1)
    x (by simpa [site,Tapes.append] using payload) (by simpa [site,Tapes.append] using head)
  have prepare := M8.Machine.ArbitraryWidthOriginalRun.extend_banks_hoare
    (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq build caller)
      (FixedHeaderBankCopy.empty 16)) M8.Machine.ArbitraryWidthHighPrepareShared.privateInput)
  rw [SharedPlacementAlphabet.setTape_append_right] at act
  rw [show volume prime v = _ from inheritedRowSwap_volume w B K s l]
  exact prepare.seq act

/-- A prepared crossing is a composable owner stage, including its header cost. -/
theorem inheritedRowSwap_stage [M8.Machine.Net] {k w B K : ℕ} (src : Fin k)
    (s : Fin 128) (l : Fin (64*64)) (hb : 0 < B) (hk : 0 < K) :
    let child := inheritedRowSwap w B K s l
    ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := volume prime child)),
      stage.cost = (2*(24*4224+333)+1)*volume prime child+1+cost child (Routines.hdr child) ∧
      ∀ data, stage.transform data = Function.update data src
        (Shared50RecursiveNodeRows.transpose (one_dvd _) (data src)) := by
  intro child
  let transform := fun data : Fin k → Fin (volume prime child) → ZMod 2 =>
    Function.update data src (Shared50RecursiveNodeRows.transpose (one_dvd _) (data src))
  let initial := (FlatCoordinateDimensions.input w K).append (FlatCoordinateDimensions.input w B)
  let finalBank := (FlatCoordinateDimensions.output (phaseField s.val (4095-l.val)) w K).append
    (FlatCoordinateDimensions.output (phaseField 0 (127-s.val+l.val)) w B)
  let bank := fun (h : Tapes 18 prime) (owners : Tapes k prime) => input (h.append owners)
  obtain ⟨slots,frame⟩ := intervalPrepared_frame (k := k) 18
  have run (data : Fin k → Fin (volume prime child) → ZMod 2) :=
    inheritedRowSwap_runs s l hb hk (phaseOwners data) src (data src) (sourceWord_cast (v := child) rfl (data src)).symm rfl
  let machineOf {t q b : ℕ} {g : Program t q prime} {pre post : Tapes t prime → Prop}
      (_ : HoareTime g pre post b) := g
  let machine := machineOf (run 0)
  refine ⟨{ tapes := _, states := _, program := machine, transform := transform,
            input := fun data => bank initial (phaseOwners data),
            output := fun data => bank finalBank (phaseOwners (transform data)),
            slots := slots, slots_injective := slots.injective,
            metadata := SharedBank.strip (bank initial (SharedBank.empty k prime)) slots,
            cost := _, input_payload := fun data => (frame _ _).1,
            output_payload := fun data => (frame _ _).1,
            strip_input := fun data => (frame _ _).2, realizes := ?_ },rfl,fun _ => rfl⟩
  intro data
  have step := run data
  have updated : setTape (phaseOwners data) src
      (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) (data src))) 0 =
      phaseOwners (transform data) := by
    rw [show sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) (data src)) = _ from sourceWord_cast (v := child) rfl (Shared50RecursiveNodeRows.transpose (one_dvd _) (data src))]
    apply congrArg₂ Tapes.mk <;> funext j <;> by_cases eq : j = src <;>
      simp [phaseOwners,transform,eq]
  rw [updated] at step
  exact step

/-- Charge all 128 header constructions, their joins to the transpose cores,
and the sequenced core calls at the same parent-volume rate. -/
theorem inheritedRowSwap_prepared_cost [M8.Machine.Net] :
    ∃ C : ℝ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
      let M := prime^w
      let V := M^128*B*M^(64*64)*K
      let view := fun s => inheritedRowSwap w B K s (inheritedLabelDigit s)
      ((128*((2*(24*4224+333)+1)*V+1)+
        ∑ s : Fin 128, (cost (view s) (Routines.hdr (view s))+1) : ℕ) : ℝ) ≤
        C*V*(w : ℝ)^M8.Machine.BudgetBound.tau := by
  obtain ⟨C,bound⟩ := inheritedRowSwap_cost
  refine ⟨C+128*(2*(24*4224+333)+2),?_⟩
  intro w B K hw hb hk M V view
  have core := bound w B K hw hb hk
  change ((∑ s : Fin 128, (cost (view s) (Routines.hdr (view s))+1) : ℕ) : ℝ) ≤
    C*V*(w : ℝ)^M8.Machine.BudgetBound.tau at core
  have hv : 0 < V := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hb) (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)) hk
  have power := Real.one_le_rpow (show 1 ≤ (w : ℝ) by exact_mod_cast hw) M8.Machine.BudgetBound.exponent_range.1.le
  have scale := le_mul_of_one_le_right (show 0 ≤ (V : ℝ) by positivity) power
  have one : 1 ≤ (V : ℝ) := by exact_mod_cast hv
  push_cast at core ⊢
  linarith only [core,scale,one]

private theorem inheritedRowSwap_cast [M8.Machine.Net] {k w B K V : ℕ} (src : Fin k)
    (s : Fin 128) (l : Fin (64*64)) (hb : 0 < B) (hk : 0 < K)
    (size : volume prime (inheritedRowSwap w B K s l) = V) :
    let v := inheritedRowSwap w B K s l
    ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)),
      stage.cost = (2*(24*4224+333)+1)*V+1+cost v (Routines.hdr v) ∧
      ∀ data, stage.transform data = Function.update data src (fun j =>
        Shared50RecursiveNodeRows.transpose (one_dvd v.rows)
          (fun i => data src (i.cast size)) (j.cast size.symm)) := by
  subst V
  exact inheritedRowSwap_stage src s l hb hk

/-- Execute every prepared crossing on one common owner bank. Only the
selected owner is updated, by the ordered fold of the 128 transposes. -/
theorem inheritedRowPlacement_stage [M8.Machine.Net] {k : ℕ} (src : Fin k) :
    ∃ C : ℝ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
      let M := prime^w
      let V := M^128*B*M^(64*64)*K
      let view := fun s => inheritedRowSwap w B K s (inheritedLabelDigit s)
      let size := fun s => inheritedRowSwap_volume w B K s (inheritedLabelDigit s)
      let move := fun (x : Fin V → ZMod 2) s (j : Fin V) =>
        Shared50RecursiveNodeRows.transpose (one_dvd (view s).rows)
          (fun i => x (i.cast (size s))) (j.cast (size s).symm)
      ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)),
        (stage.cost : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau ∧
        ∀ data, stage.transform data = Function.update data src ((List.finRange 128).foldl move (data src)) := by
  obtain ⟨C,bound⟩ := inheritedRowSwap_prepared_cost
  refine ⟨C,?_⟩
  intro w B K hw hb hk M V view size move
  choose stages paid act using fun s => inheritedRowSwap_cast src s (inheritedLabelDigit s) hb hk (size s)
  let hk' : 0 < k := Nat.zero_lt_of_lt src.isLt
  refine ⟨SharedBankStage.compile _ hk' (List.ofFn stages),?_,?_⟩
  · rw [SharedBankStage.compile_cost,List.length_ofFn,List.map_ofFn,List.sum_ofFn]
    let prep := (2*(24*4224+333)+1)*V+1
    let price := fun s => cost (view s) (Routines.hdr (view s))
    have costs : SharedBankStage.Stage.cost ∘ stages = fun s => prep+price s := funext paid
    rw [costs]
    have sumCosts {n : ℕ} (f : Fin n → ℕ) (a : ℕ) :
        (∑ i, (a+f i))+n = n*a+∑ i, (f i+1) := by
      simp [Finset.sum_add_distrib,Nat.add_assoc]
    rw [sumCosts]
    exact bound w B K hw hb hk
  · intro data
    rw [SharedBankStage.compile_transform,SharedBankStage.execute,List.ofFn_eq_map,List.foldl_map]
    have fold (ss : List (Fin 128)) (x : Fin V → ZMod 2) :
        ss.foldl (fun d s => (stages s).transform d) (Function.update data src x) =
          Function.update data src (ss.foldl move x) := by
      induction ss generalizing x with
      | nil => rfl
      | cons s ss ih =>
        simp only [List.foldl_cons]
        rw [act s (Function.update data src x)]
        simp only [Function.update_self,Function.update_idem]
        exact ih (move x s)
    simpa only [Function.update_eq_self] using fold (List.finRange 128) (data src)

/-- Read the compiled placement at an arbitrary inherited address. The block
and trailing cell retain their positions while the two label rows change places
with the external fields. -/
theorem inheritedRowPlacement_read [M8.Machine.Net] {k : ℕ} (src : Fin k) :
    ∃ C : ℝ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
      let V := (prime^w)^128*B*(prime^w)^(64*64)*K
      ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)),
        (stage.cost : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau ∧
        ∀ data, (∀ j, j ≠ src → stage.transform data j = data j) ∧
          ∀ (x : Fin 128 ⊕ Fin (64*64) → ZMod (prime^w)) (b : Fin B) (t : Fin K), ext (stage.transform data src) (inheritedDigitCell x b t) =
            ext (data src) (inheritedDigitCell (x ∘ remainderRowPlacement) b t) := by
  obtain ⟨C,compile⟩ := inheritedRowPlacement_stage src
  refine ⟨C,?_⟩
  intro w B K hw hb hk V
  obtain ⟨stage,paid,action⟩ := compile w B K hw hb hk
  refine ⟨stage,paid,?_⟩
  intro data
  rw [action]
  refine ⟨fun j hj => Function.update_of_ne hj ..,?_⟩
  intro x b t
  rw [Function.update_self]
  let view := fun s => inheritedRowSwap w B K s (inheritedLabelDigit s)
  let size := fun s => inheritedRowSwap_volume w B K s (inheritedLabelDigit s)
  let move := fun (v : Fin V → ZMod 2) s (j : Fin V) =>
    Shared50RecursiveNodeRows.transpose (one_dvd (view s).rows) (fun i => v (i.cast (size s))) (j.cast (size s).symm)
  let swap := fun s => Equiv.swap (Sum.inl s) (Sum.inr (inheritedLabelDigit s))
  have single (v : Fin V → ZMod 2) s (digits : Fin 128 ⊕ Fin (64*64) → ZMod (prime^w)) :
      ext (move v s) (inheritedDigitCell digits b t) =
        ext v (inheritedDigitCell (digits ∘ swap s) b t) := by
    have read := inheritedRowSwap_digits s (inheritedLabelDigit s) (fun i => v (i.cast (size s)))
      (digits ∘ swap s) b t
    have undo : (digits ∘ swap s) ∘ swap s = digits := by funext j; simp [swap]
    change ext _ (inheritedDigitCell ((digits ∘ swap s) ∘ swap s) b t) = _ at read
    rw [undo,ext_cast] at read
    unfold move
    rwa [ext_cast]
  have fold (ss : List (Fin 128)) (v : Fin V → ZMod 2) (digits : Fin 128 ⊕ Fin (64*64) → ZMod (prime^w)) :
      ext (ss.foldl move v) (inheritedDigitCell digits b t) =
        ext v (inheritedDigitCell (fun j => digits (ss.foldl (fun a s => swap s a) j)) b t) := by
    induction ss generalizing v digits with
    | nil => rfl
    | cons s ss ih =>
      simp only [List.foldl_cons]
      exact (ih (move v s) digits).trans (single v s _)
  simpa only [swap,inheritedRowSwap_schedule,Function.comp_def] using fold (List.finRange 128) (data src) x

section
local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩

/-- The chart sees the external field rank as its outer row and the block
as its label prefix. Thus chart transport uses the inherited owner offset. -/
private theorem inheritedChart_general {n m w B K : ℕ} {x y : ℕ → ZMod 2}
    {f : LabelPadding.Label m w → LabelPadding.Label m w} :
    let M := prime^w
    let v : Descriptor := ⟨M^n,1,B*prime^(m*(w*m)),0,1,K⟩
    LabelPermutation.Transport v B w f x y →
    ∀ (digits : Fin n ⊕ Fin (m*m) → ZMod M) (b : Fin B) (t : Fin K),
      let g : LabelPadding.Label m w := fun r i => digits (.inr (finProdFinEquiv (i,r)))
      let out := Sum.elim (digits ∘ Sum.inl) (M8.AtomOps.refine (Route.cols (f g)))
      let cell := fun (z : Fin n ⊕ Fin (m*m) → ZMod M) =>
        (((FlatCoordinateLayout.rank (z ∘ Sum.inl)).val*B+b.val)*M^(m*m)+(FlatCoordinateLayout.rank (z ∘ Sum.inr)).val)*K+t.val
      y (cell out) = x (cell digits) := by
  intro M v run digits b t g out cell
  let field := FlatCoordinateLayout.rank (digits ∘ Sum.inl)
  have same : M8.AtomOps.refine (Route.cols g) = digits ∘ Sum.inr := by
    funext j
    obtain ⟨⟨i,r⟩,rfl⟩ := (@finProdFinEquiv m m).surjective j
    simp [M8.AtomOps.refine,Route.cols,g]
  have radix : prime^(m*(w*m)) = M^(m*m) := by
    dsimp [M]; rw [← pow_mul]; congr 1; ring
  have read := run g field.val field.isLt 0 Nat.zero_lt_one b.val b.isLt 0 (by simp [v])
    0 Nat.zero_lt_one 0 (by simp [v]) t.val t.isLt
  have left : out ∘ Sum.inl = digits ∘ Sum.inl := rfl
  have right : out ∘ Sum.inr = M8.AtomOps.refine (Route.cols (f g)) := rfl
  simp only [cell,left,right]
  simp only [RecursiveInterchangeLayout.index,v,radix,field,LabelAddress.address,same,
    pow_zero,Nat.mul_one,Nat.add_zero] at read
  have join (a n z : ℕ) : a*(B*n)+(b.val*n+z) = (a*B+b.val)*n+z := by ring
  simp only [join] at read
  exact read

/-- The chart sees the external field rank as its outer row and the block
as its label prefix. Thus chart transport uses the inherited owner offset. -/
theorem inheritedChart_read {w B K : ℕ} {x y : ℕ → ZMod 2}
    {f : LabelPadding.Label 64 w → LabelPadding.Label 64 w} :
    let M := prime^w
    let v : Descriptor := ⟨M^128,1,B*prime^(64*(w*64)),0,1,K⟩
    LabelPermutation.Transport v B w f x y →
    ∀ (digits : Fin 128 ⊕ Fin (64*64) → ZMod M) (b : Fin B) (t : Fin K),
      let g : LabelPadding.Label 64 w := fun r i => digits (.inr (finProdFinEquiv (i,r)))
      let out := Sum.elim (digits ∘ Sum.inl) (M8.AtomOps.refine (Route.cols (f g)))
      y (inheritedDigitCell out b t) = x (inheritedDigitCell digits b t) := inheritedChart_general (n := 128) (m := 64)

/-- Both placements and the intervening chart read the same physical block
and trailing position throughout the three stages. -/
theorem inheritedPlacedChart_read {w B K : ℕ} {x p q y : ℕ → ZMod 2}
    {f : LabelPadding.Label 64 w → LabelPadding.Label 64 w} :
    let M := prime^w
    let v : Descriptor := ⟨M^128,1,B*prime^(64*(w*64)),0,1,K⟩
    let placement := fun (u v : ℕ → ZMod 2) => ∀ (d : Fin 128 ⊕ Fin (64*64) → ZMod M)
      (b : Fin B) (t : Fin K), v (inheritedDigitCell d b t) = u (inheritedDigitCell (d ∘ remainderRowPlacement) b t)
    placement x p → LabelPermutation.Transport v B w f p q → placement q y →
    ∀ (digits : Fin 128 ⊕ Fin (64*64) → ZMod M) (b : Fin B) (t : Fin K),
      let parked := digits ∘ remainderRowPlacement
      let g : LabelPadding.Label 64 w := fun r i => parked (.inr (finProdFinEquiv (i,r)))
      let charted := Sum.elim (parked ∘ Sum.inl) (M8.AtomOps.refine (Route.cols (f g)))
      y (inheritedDigitCell (charted ∘ remainderRowPlacement) b t) = x (inheritedDigitCell digits b t) := by
  intro M v placement enter chart back digits b t parked g charted
  have twice (d : Fin 128 ⊕ Fin (64*64) → ZMod M) :
      (d ∘ remainderRowPlacement) ∘ remainderRowPlacement = d := by
    funext j
    exact congrArg d (remainderRowPlacement.symm_apply_apply j)
  have leave := back (charted ∘ remainderRowPlacement) b t
  rw [twice] at leave
  have start := enter (digits ∘ remainderRowPlacement) b t
  rw [twice] at start
  exact leave.trans ((inheritedChart_read chart parked b t).trans start)

/-- Execute a chart between the two inherited placements, on the same owner
tape and at every block index. Both joins and all crossing headers are charged. -/
theorem inheritedPlacedChart_stage [M8.Machine.Net] {k : ℕ} (src : Fin k)
    (c : PortCertificate) (hc : c.Checked) (inverse : Bool) :
    ∃ C : ℝ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
      let M := prime^w
      let V := M^128*B*M^(64*64)*K
      let H := c.fullChart.submatrix stageAxis.symm remainderAxis
      let σ := reduce M (if inverse then H.transpose else H)
      ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)),
        (stage.cost : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau ∧
        ∀ data, (∀ j, j ≠ src → stage.transform data j = data j) ∧
          ∀ (digits : Fin 128 ⊕ Fin (64*64) → ZMod M) (b : Fin B) (t : Fin K),
            let parked := digits ∘ remainderRowPlacement
            let g : LabelPadding.Label 64 w := fun r i => parked (.inr (finProdFinEquiv (i,r)))
            let charted := Sum.elim (parked ∘ Sum.inl) (M8.AtomOps.refine (Route.cols (g*σ)))
            ext (stage.transform data src) (inheritedDigitCell (charted ∘ remainderRowPlacement) b t) =
              ext (data src) (inheritedDigitCell digits b t) := by
  obtain ⟨P,place⟩ := inheritedRowPlacement_read src
  obtain ⟨A,_,chart⟩ := remainderChart_stage src c hc inverse
  obtain ⟨Q,bound⟩ := scaledRoute_cost_bound A 63 64 (by decide)
  refine ⟨2*P+Q+2,?_⟩
  intro w B K hw hb hk M V H σ
  let v : Descriptor := ⟨M^128,1,B*prime^(64*(w*64)),0,1,K⟩
  have pos : v.Positive := ⟨pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _,
    Nat.zero_lt_one,Nat.mul_pos hb (pow_pos Shared50ModularControl.prime_prime.pos _),Nat.zero_lt_one,hk⟩
  have radix : prime^(64*(w*64)) = M^(64*64) := by
    dsimp [M]; rw [← pow_mul]; congr 1; ring
  have size : volume prime v = V := by
    simp only [volume,v,V,radix,pow_zero,mul_one]; ring
  let spec := fun N => ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := N)),
    stage.cost = A*N+63*LeafCore.coreCost N (w*64) ∧
    ∀ data, (∀ j, j ≠ src → stage.transform data j = data j) ∧
      LabelPermutation.Transport v B w (fun g => g*σ) (ext (data src)) (ext (stage.transform data src))
  have supplied : spec (volume prime v) := by
    obtain ⟨stage,_,bill,_,reads⟩ := chart v w B hw hb rfl pos
    exact ⟨stage,bill,reads⟩
  rw [size] at supplied
  obtain ⟨middle,costEq,transport⟩ := supplied
  obtain ⟨swap,paid,placed⟩ := place w B K hw hb hk
  refine ⟨SharedBankStage.compose (SharedBankStage.compose swap middle) swap,?_,?_⟩
  · change ((swap.cost+middle.cost+1+swap.cost+1 : ℕ) : ℝ) ≤ _
    have bill := bound V w hw
    rw [← costEq] at bill
    have hv : 0 < V := size ▸ RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v pos
    have one : 1 ≤ (V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau :=
      one_le_mul_of_one_le_of_one_le (by exact_mod_cast hv)
        (Real.one_le_rpow (by exact_mod_cast hw) M8.Machine.BudgetBound.exponent_range.1.le)
    push_cast
    linarith only [bill,paid,one]
  · intro data
    obtain ⟨off,enter⟩ := placed data
    obtain ⟨keep,run⟩ := transport (swap.transform data)
    obtain ⟨outside,back⟩ := placed (middle.transform (swap.transform data))
    exact ⟨fun j hj => (outside j hj).trans ((keep j hj).trans (off j hj)),
      inheritedPlacedChart_read (w := w) (B := B) (K := K) (f := fun g => g*σ) (x := ext (data src)) (p := ext (swap.transform data src)) (q := ext (middle.transform (swap.transform data) src)) (y := ext (swap.transform (middle.transform (swap.transform data)) src)) enter run back⟩

end

/-- Both directions of the scheduled chart act on the packed record word consumed by the parent. -/
theorem packedRemainderChart_stage [M8.Machine.Net] {k : ℕ} (src : Fin k) (c : PortCertificate)
    (hc : c.Checked) (inverse : Bool) :
    let H := c.fullChart.submatrix stageAxis.symm remainderAxis
    let σ := if inverse then H.transpose else H
    ∃ (C : ℕ) (machine : SharedBankSkeleton.Skeleton k prime), ∀ (layout : Descriptor) (w rows B : ℕ), layout.Positive →
      layout.width = 64*(w+1) → layout.rows = 142080*rows →
      layout.beforeH = B*prime^(64*((w+1)*64)) →
      let v := role layout 142080
      let N := LabelMask.records v*((prime^(w+1))^128*(layout.between*layout.afterD))
      let spec := fun n : ℕ =>
      ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := n)),
        RemainderChartFrame machine v (w+1) stage ∧
        (∀ width : ℕ, (w+1)*64 ≤ width → ((stage.cost*(stage.tapes+5) : ℕ) : ℝ) ≤
          (((C : ℝ)+63*|LeafCore.C| * (width : ℝ)^M8.Machine.BudgetBound.tau)*n)*(machine.tapes+5)) ∧
        ∀ data, (∀ j, j ≠ src → stage.transform data j = data j) ∧
          LabelPermutation.Transport v B (w+1)
            (fun g => g * reduce (modulus (w+1)) σ)
            (ext (data src)) (ext (stage.transform data src))
      spec N := by
  intro H σ
  obtain ⟨C,machine,chart⟩ := remainderChart_stage src c hc inverse
  refine ⟨C,machine,?_⟩
  intro layout w rows B positive width split shape v N spec
  have pos := RecursiveRowsNodeLayout.role_positive 142080 layout (by decide) positive ⟨rows,split⟩
  have hb : 0 < B := by
    by_contra! h
    have := positive.2.2.1
    simp [Nat.eq_zero_of_le_zero h] at shape
    omega
  have size : volume prime v = N := by
    simp only [N,v,LabelMask.records,role,volume,width,show 64*(w+1) = (w+1)*64 by omega,
      pow_mul,show (128 : ℕ) = 64+64 by decide,pow_add]
    ac_rfl
  obtain ⟨stage,frame,_,time,action⟩ := chart v (w+1) B (by omega) hb shape pos
  change spec N
  rw [← size]
  exact ⟨stage,frame,time,action⟩

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
  obtain ⟨A,_,enter⟩ := remainderChart_stage src c hc false
  obtain ⟨D,_,leave⟩ := remainderChart_stage src c hc true
  refine ⟨A+(2*(24*64+333)+250)+D,?_⟩
  intro w B K hw hb hk W v V child hs H
  have pos := Shared50ModularControl.prime_prime.pos
  have hW : 0 < W := by dsimp [W]; positivity
  have vp : v.Positive := ⟨pow_pos (pow_pos pos _) _,Nat.zero_lt_one,Nat.mul_pos hb (pow_pos pos _),Nat.zero_lt_one,hk⟩
  have flat : V = (prime^w)^128*W := by simp [V,v,volume,W,Nat.mul_assoc]
  obtain ⟨ordered,fit,_⟩ := BitHosting.remainder_counts e he
  have size : volume prime child = V := (intervalChild_volume ordered (show e.2 ≤ 64 by omega) w W).trans flat.symm
  obtain ⟨s,_,bs,_,es⟩ := enter v w B hw hb rfl vp
  obtain ⟨m,bm,em⟩ := remainderOwner_flat src e he hw hW size
  obtain ⟨t,_,bt,_,et⟩ := leave v w B hw hb rfl vp
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
