import IntegerMultBounds.Machine.RecursiveInterchangeVolume
import Mathlib.Data.Nat.Log
import IntegerMultBounds.Machine.GrowingCounterData

/-! Descriptor-size comparison along recursive child selections. Retained
spectator digits ensure that the root's binary size is at most a fixed multiple
of the current child's binary size, despite cyclic row subdivision. This is
arithmetic, not an assertion that descriptor processing is free. -/
namespace IntegerMultBounds.Machine.RecursiveDescriptorSize
open RecursiveInterchangeLayout RecursiveInterchangeVolume

private theorem exponent_le_power (m k : ℕ) (hm : 2 ≤ m) : k ≤ m^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have hp : 0 < m^k := pow_pos (by omega) _
    nlinarith

theorem depth_le_child_log {q roles m n k : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive) :
    n ≤ Nat.log2 (volume q v) := by
  have hl := path.original_chunks (by omega) hr hv
  have hqpow : 0 < q^root.width := pow_pos (by omega) _
  have hroot : 2^root.width ≤ volume q v := by
    calc
      _ ≤ q^root.width := Nat.pow_le_pow_left hq _
      _ ≤ q^root.width*q^root.width := Nat.le_mul_of_pos_right _ hqpow
      _ = q^(2*root.width) := by rw [two_mul,pow_add]
      _ ≤ _ := hl
  have hpos : 0 < volume q v := lt_of_lt_of_le (pow_pos (by decide : 0 < 2) _) hroot
  have hlog : root.width ≤ Nat.log2 (volume q v) := (Nat.le_log2 (by omega)).mpr hroot
  have hd := path.depth_bound (by omega) hw
  have he := exponent_le_power m k hm
  omega

/-- The fixed factor depends on role count alone, never recursion depth or
runtime field lengths. The +1 convention covers exact powers of two. -/
theorem root_log_width_le {q roles m n k : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive) :
    Nat.log2 (volume q root)+1 ≤ (Nat.log2 roles+2)*(Nat.log2 (volume q v)+1) := by
  have hl := path.original_chunks (by omega) hr hv
  have hpos : 0 < volume q v := lt_of_lt_of_le (pow_pos (by omega : 0 < q) _) hl
  have hroot : 0 < volume q root := by
    rw [← path.volume_mul]
    exact Nat.mul_pos hpos (pow_pos hr _)
  have hc : volume q v < 2^(Nat.log2 (volume q v)+1) :=
    (Nat.log2_lt (by omega)).mp (by omega)
  have hroles : roles < 2^(Nat.log2 roles+1) := (Nat.log2_lt (by omega)).mp (by omega)
  have hp : roles^n ≤ 2^((Nat.log2 roles+1)*n) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_of_lt hroles) n
  have hx : volume q root < 2^(Nat.log2 (volume q v)+1+(Nat.log2 roles+1)*n) := by
    rw [← path.volume_mul,pow_add]
    calc
      _ ≤ volume q v*2^((Nat.log2 roles+1)*n) := Nat.mul_le_mul_left _ hp
      _ < _ := Nat.mul_lt_mul_of_pos_right hc (pow_pos (by decide : 0 < 2) _)
  have he : Nat.log2 (volume q root) < Nat.log2 (volume q v)+1+(Nat.log2 roles+1)*n :=
    (Nat.log2_lt (by omega)).mpr hx
  have hd := depth_le_child_log path hq hr hm hw hv
  have hb := Nat.mul_le_mul_left (Nat.log2 roles+1) hd
  nlinarith

/-- A canonical descriptor for any root-bounded quantity has only a fixed
multiple of the current child's binary size, including zero-valued fields. -/
theorem descriptor_length_le_child_log {q roles m n k : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (bs : List Bool) (hc : GrowingCounterData.Canonical bs)
    (hb : Counter.value bs ≤ volume q root) :
    bs.length ≤ (Nat.log2 roles+2)*(Nat.log2 (volume q v)+1) := by
  have hm' : Nat.log2 (Counter.value bs) ≤ Nat.log2 (volume q root) := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.log_mono_right hb
  exact (GrowingCounterData.canonical_width bs hc).trans
    ((Nat.add_le_add_right hm' 1).trans (root_log_width_le path hq hr hm hw hv))

/-- In particular every constant number of descriptor scans is charged to
logical child volume rather than the size of parked ancestor storage. -/
theorem descriptor_length_le_volume {q roles m n k : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (bs : List Bool) (hc : GrowingCounterData.Canonical bs)
    (hb : Counter.value bs ≤ volume q root) :
    bs.length ≤ (2*(Nat.log2 roles+2))*volume q v := by
  have hl := path.original_chunks (by omega) hr hv
  have hp : 0 < volume q v := lt_of_lt_of_le (pow_pos (by omega : 0 < q) _) hl
  have hh := Nat.log2_le_self (volume q v)
  have hlog : Nat.log2 (volume q v)+1 ≤ 2*volume q v := by omega
  have hb' := Nat.mul_le_mul_left (Nat.log2 roles+2) hlog
  have hlen := descriptor_length_le_child_log path hq hr hm hw hv bs hc hb
  nlinarith

end IntegerMultBounds.Machine.RecursiveDescriptorSize
