import IntegerMultBounds.Machine.RecursiveDescriptorSize
import IntegerMultBounds.Machine.BinaryDivide

/-! The existing physical long-division scan has a linear logical-child-volume
bound for canonical root-bounded descriptors. Its shifted output origins and
noncanonical quotient remain explicit; normalization is a separate operation. -/
namespace IntegerMultBounds.Machine.RecursiveDescriptorDivision
open RecursiveInterchangeLayout RecursiveInterchangeVolume

theorem square_succ_le_pow (k : ℕ) : (k+1)^2 ≤ 4*2^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    by_cases hk : k < 2
    · interval_cases k <;> norm_num
    · simp only [pow_succ 2 k]
      have hk2 : 2 ≤ k := by omega
      have hkk : 4 ≤ k*k := by nlinarith
      nlinarith

theorem square_log_le (V : ℕ) (hV : 0 < V) : (Nat.log2 V+1)^2 ≤ 4*V := by
  have hp : 2^Nat.log2 V ≤ V := (Nat.le_log2 (by omega)).mp le_rfl
  exact (square_succ_le_pow _).trans (Nat.mul_le_mul_left _ hp)

theorem quadratic_cost_le (V C L D : ℕ) (hV : 0 < V)
    (hL : L ≤ C*(Nat.log2 V+1)) (hD : D ≤ C*(Nat.log2 V+1)) :
    L*(4*L+6*D+27) ≤ (40*C^2+54*C)*V := by
  have hlog : Nat.log2 V+1 ≤ 2*V := by have := Nat.log2_le_self V; omega
  have hsq := square_log_le V hV
  calc
    _ ≤ (C*(Nat.log2 V+1))*(4*(C*(Nat.log2 V+1))+6*(C*(Nat.log2 V+1))+27) :=
      Nat.mul_le_mul hL (by omega)
    _ = 10*C^2*(Nat.log2 V+1)^2+27*C*(Nat.log2 V+1) := by ring
    _ ≤ 10*C^2*(4*V)+27*C*(2*V) := Nat.add_le_add
      (Nat.mul_le_mul_left _ hsq) (Nat.mul_le_mul_left _ hlog)
    _ = _ := by ring

/-- Bound the exact sum of transitions of BinaryDivide.program, without
pretending descriptor division or moving output origins is free. -/
theorem cost_le_child_volume {q roles m n k : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (ys ds : List Bool) (hy : GrowingCounterData.Canonical ys)
    (hd : GrowingCounterData.Canonical ds)
    (hyv : Counter.value ys ≤ volume q root) (hdv : Counter.value ds ≤ volume q root) :
    ∑ i ∈ Finset.range ys.length, (BinaryDivide.costAt ys ds i+2) ≤
      (40*(Nat.log2 roles+2)^2+54*(Nat.log2 roles+2))*volume q v := by
  have hp := path.original_chunks (by omega) hr hv
  have hV : 0 < volume q v := lt_of_lt_of_le (pow_pos (by omega : 0 < q) _) hp
  exact (BinaryDivide.cost_le ys ds).trans (quadratic_cost_le _ _ _ _ hV
    (RecursiveDescriptorSize.descriptor_length_le_child_log path hq hr hm hw hv ys hy hyv)
    (RecursiveDescriptorSize.descriptor_length_le_child_log path hq hr hm hw hv ds hd hdv))

/-- The physical five-tape division routine with its original exact bank
contract and a child-volume transition bound. Header normalization is not hidden. -/
theorem divide_hoare_linear {q roles m n k a : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (ys ds : List Bool) (hy : GrowingCounterData.Canonical ys)
    (hd : GrowingCounterData.Canonical ds)
    (hyv : Counter.value ys ≤ volume q root) (hdv : Counter.value ds ≤ volume q root)
    (f g : ℤ → Fin (a+4)) (pn pd pr pf pq : ℤ)
    (hfl : f (pn-1) = blank) (hgr : g (pd+ds.length) = blank) (hgl : g (pd-1) = blank) :
    HoareTime (BinaryDivide.program a)
      (fun w => w = BinaryDivide.bank (putWord f pn (ys.map bitSymbol))
        (putWord g pd (ds.map bitSymbol)) (fun _ => blank) (fun _ => blank) (fun _ => blank)
        (pn+ys.length-1) pd pr pf pq)
      (fun w => w = BinaryDivide.bank (putWord f pn (ys.map bitSymbol))
        (putWord g pd (ds.map bitSymbol))
        (BinaryDivide.blankWord (pr-ys.length) (BinaryDivide.remainder ds ys)) (fun _ => blank)
        (BinaryDivide.blankWord (pq-ys.length) (BinaryDivide.quotient ds ys))
        (pn-1) pd (pr-ys.length) pf (pq-ys.length))
      ((40*(Nat.log2 roles+2)^2+54*(Nat.log2 roles+2))*volume q v) :=
  (BinaryDivide.divide_hoare ys ds f g pn pd pr pf pq hfl hgr hgl).consequence
    (fun _ h => h) (fun _ h => h)
    (cost_le_child_volume path hq hr hm hw hv ys ds hy hd hyv hdv)

end IntegerMultBounds.Machine.RecursiveDescriptorDivision
