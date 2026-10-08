import IntegerMultBounds.Machine.BinaryDescriptorDivision
import IntegerMultBounds.Machine.RecursiveDescriptorDivision

/-! Fully prepared, canonical-output, physically cleaned binary descriptor
division charged to the active child's logical volume. Every boundary scan,
marker operation, tracked transition and scratch cleanup is included. -/
namespace IntegerMultBounds.Machine.RecursiveCleanDescriptorDivision
open RecursiveInterchangeLayout RecursiveInterchangeVolume

theorem cost_le_child_volume {q roles m n k : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (ys ds : List Bool) (hy : GrowingCounterData.Canonical ys) (hd : GrowingCounterData.Canonical ds)
    (hyv : Counter.value ys ≤ volume q root) (hdv : Counter.value ds ≤ volume q root) :
    BinaryDescriptorDivision.cost ys ds ≤
      (1280*(Nat.log2 roles+2)^2+1920*(Nat.log2 roles+2)+710)*volume q v := by
  have hdiv := RecursiveDescriptorDivision.cost_le_child_volume path hq hr hm hw hv ys ds hy hd hyv hdv
  have hlen := RecursiveDescriptorSize.descriptor_length_le_volume path hq hr hm hw hv ys hy hyv
  have hpos : 0 < volume q v := lt_of_lt_of_le (pow_pos (by omega : 0 < q) _)
    (path.original_chunks (by omega) hr hv)
  unfold BinaryDescriptorDivision.cost BinaryDescriptorDivision.coreCost
  nlinarith

/-- Exact retained canonical inputs and canonical quotient, all other tapes
literally blank at head zero. This is a concrete fixed program, not a cost oracle. -/
theorem divide_hoare_linear {q roles m n k a : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (ys ds : List Bool) (hy : GrowingCounterData.Canonical ys) (hd : GrowingCounterData.Canonical ds)
    (hyv : Counter.value ys ≤ volume q root) (hdv : Counter.value ds ≤ volume q root)
    (hdpos : 0 < Counter.value ds) :
    ∃ zs : List Bool, GrowingCounterData.Canonical zs ∧ Counter.value zs = Counter.value ys / Counter.value ds ∧
      zs.length ≤ ys.length ∧
      HoareTime (BinaryDescriptorDivision.program a) (fun w => w = BinaryDescriptorDivision.input ys ds)
        (fun w => w = BinaryDescriptorDivision.output ys ds zs)
        ((1280*(Nat.log2 roles+2)^2+1920*(Nat.log2 roles+2)+710)*volume q v) := by
  obtain ⟨zs,hc,hval,hlen,hprog⟩ := BinaryDescriptorDivision.divide_hoare (a := a) ys ds hdpos
  exact ⟨zs,hc,hval,hlen,hprog.consequence (fun _ h => h) (fun _ h => h)
    (cost_le_child_volume path hq hr hm hw hv ys ds hy hd hyv hdv)⟩

end IntegerMultBounds.Machine.RecursiveCleanDescriptorDivision
