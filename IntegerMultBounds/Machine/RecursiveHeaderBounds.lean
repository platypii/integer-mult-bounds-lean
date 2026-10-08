import IntegerMultBounds.Machine.RecursiveDimensionBank
import IntegerMultBounds.Machine.RecursiveDescriptorSize

/-! Actual six-field layout headers satisfy the root-volume hypotheses used by
recursive descriptor-stack bounds. No external size certificate is required. -/
namespace IntegerMultBounds.Machine.RecursiveHeaderBounds
open RecursiveInterchangeLayout RecursiveInterchangeVolume RecursiveDimensionBank

theorem values_le_volume {q : ℕ} (hq : 2 ≤ q) (v : Descriptor) (hv : v.Positive)
    (i : Fin 6) : values v i ≤ volume q v := by
  rcases hv with ⟨hA,hR,hB,hC,hE⟩
  have hQ : 0 < q^v.width := pow_pos (by omega) _
  have hw : v.width ≤ q^v.width := by
    induction v.width with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      have hp : 0 < q^k := pow_pos (by omega) _
      nlinarith
  have hprod (a b c d e f g : ℕ) (hb : 0 < b) (hc : 0 < c)
      (hd : 0 < d) (he : 0 < e) (hf : 0 < f) (hg : 0 < g) :
      a ≤ a*b*c*d*e*f*g := by
    exact le_trans (Nat.le_mul_of_pos_right a hb)
      (le_trans (Nat.le_mul_of_pos_right _ hc)
      (le_trans (Nat.le_mul_of_pos_right _ hd)
      (le_trans (Nat.le_mul_of_pos_right _ he)
      (le_trans (Nat.le_mul_of_pos_right _ hf) (Nat.le_mul_of_pos_right _ hg)))))
  have hbase : q^v.width ≤ volume q v := by
    convert hprod (q^v.width) v.beforeRows v.rows v.beforeH v.between (q^v.width) v.afterD hA hR hB hC hQ hE using 1
    simp only [volume]
    ring
  fin_cases i
  · exact hprod _ _ _ _ _ _ _ hR hB hQ hC hQ hE
  · convert hprod v.rows v.beforeRows v.beforeH (q^v.width) v.between (q^v.width) v.afterD hA hB hQ hC hQ hE using 1 <;> first | rfl | (simp only [volume]; ring)
  · convert hprod v.beforeH v.beforeRows v.rows (q^v.width) v.between (q^v.width) v.afterD hA hR hQ hC hQ hE using 1 <;> first | rfl | (simp only [volume]; ring)
  · exact hw.trans hbase
  · convert hprod v.between v.beforeRows v.rows v.beforeH (q^v.width) (q^v.width) v.afterD hA hR hB hQ hQ hE using 1 <;> first | rfl | (simp only [volume]; ring)
  · convert hprod v.afterD v.beforeRows v.rows v.beforeH (q^v.width) v.between (q^v.width) hA hR hB hQ hC hQ using 1 <;> first | rfl | (simp only [volume]; ring)

theorem headers_root_bounded {q roles m n : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) (hq : 2 ≤ q) (hr : 0 < roles)
    (hv : root.Positive) (hs : Fin 6 → List Bool) (hh : Headers v hs) (i : Fin 6) :
    Counter.value (hs i) ≤ volume q root := by
  rw [hh.1 i, ← path.volume_mul]
  exact (values_le_volume hq v (path.positive (by omega) hr hv) i).trans
    (Nat.le_mul_of_pos_right _ (pow_pos hr _))

/-- Every real layout header has the required child-volume scan bound. -/
theorem header_length_le {q roles m n k : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (hs : Fin 6 → List Bool) (hh : Headers v hs) (i : Fin 6) :
    (hs i).length ≤ (2*(Nat.log2 roles+2))*volume q v :=
  RecursiveDescriptorSize.descriptor_length_le_volume path hq hr hm hw hv (hs i)
    (hh.2 i) (headers_root_bounded path hq hr hv hs hh i)

/-- Saved ancestor headers may be scanned at a deeper active child. Both paths
share the original root, so parked ancestor volume is never charged as work. -/
theorem saved_header_length_le {q roles m n d k : ℕ} {root v saved : Descriptor}
    (current : Path q roles m root n v) (older : Path q roles m root d saved)
    (hq : 2 ≤ q) (hr : 0 < roles) (hm : 2 ≤ m)
    (hw : root.width = m^k) (hv : root.Positive)
    (hs : Fin 6 → List Bool) (hh : Headers saved hs) (i : Fin 6) :
    (hs i).length ≤ (2*(Nat.log2 roles+2))*volume q v :=
  RecursiveDescriptorSize.descriptor_length_le_volume current hq hr hm hw hv (hs i)
    (hh.2 i) (headers_root_bounded older hq hr hv hs hh i)

end IntegerMultBounds.Machine.RecursiveHeaderBounds
