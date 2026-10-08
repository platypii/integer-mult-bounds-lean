import IntegerMultBounds.Machine.BinaryDivideQuotient
import IntegerMultBounds.Machine.RecursiveDescriptorDivision

/-! Physical quotient relocation and canonicalization retain the long-division
child-volume bound. Raw input preparation and remainder cleanup remain explicit
in BinaryDivideQuotient.input/output; this theorem does not hide either task. -/
namespace IntegerMultBounds.Machine.RecursiveQuotientDivision
open RecursiveInterchangeLayout RecursiveInterchangeVolume

theorem divide_hoare_linear {q roles m n k a : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (ys ds : List Bool) (hy : GrowingCounterData.Canonical ys) (hd : GrowingCounterData.Canonical ds)
    (hyv : Counter.value ys ≤ volume q root) (hdv : Counter.value ds ≤ volume q root)
    (hdpos : 0 < Counter.value ds) :
    ∃ zs : List Bool, GrowingCounterData.Canonical zs ∧ Counter.value zs = Counter.value ys / Counter.value ds ∧
      zs.length ≤ ys.length ∧
      HoareTime (BinaryDivideQuotient.program a) (fun w => w = BinaryDivideQuotient.input ys ds)
        (fun w => w = BinaryDivideQuotient.output ys ds zs)
        ((40*(Nat.log2 roles+2)^2+58*(Nat.log2 roles+2)+9)*volume q v) := by
  obtain ⟨zs,hc,hval,hlen,hprog⟩ := BinaryDivideQuotient.divide_hoare (a := a) ys ds hdpos
  refine ⟨zs,hc,hval,hlen,hprog.consequence (fun _ h => h) (fun _ h => h) ?_⟩
  have hdiv := RecursiveDescriptorDivision.cost_le_child_volume path hq hr hm hw hv ys ds hy hd hyv hdv
  have hlen := RecursiveDescriptorSize.descriptor_length_le_volume path hq hr hm hw hv ys hy hyv
  have hpos : 0 < volume q v := lt_of_lt_of_le (pow_pos (by omega : 0 < q) _)
    (path.original_chunks (by omega) hr hv)
  nlinarith

end IntegerMultBounds.Machine.RecursiveQuotientDivision
