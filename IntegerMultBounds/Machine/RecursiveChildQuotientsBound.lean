import IntegerMultBounds.Machine.RecursiveChildQuotients
import IntegerMultBounds.Machine.RecursiveDescriptorDivision
import IntegerMultBounds.Machine.RecursiveHeaderBounds

/-! Child quotient generation has a logical-child-volume bound. Fixed divisor
bit lengths belong to the compile-time constant; no assumption that these
constants fit below root volume is needed. -/
namespace IntegerMultBounds.Machine.RecursiveChildQuotientsBound
open RecursiveInterchangeLayout RecursiveInterchangeVolume RecursiveDimensionBank

theorem fixed_divisor_cost (ys ds : List Bool) (C V : ℕ) (hV : 0 < V)
    (hy : ys.length ≤ C*(Nat.log2 V+1)) :
    BinaryDescriptorDivision.cost ys ds ≤
      (512*C^2+(384*ds.length+1920)*C+710)*V := by
  have hlog : Nat.log2 V+1 ≤ 2*V := by have := Nat.log2_le_self V; omega
  have hlin : ys.length ≤ 2*C*V := by
    have h := hy.trans (Nat.mul_le_mul_left C hlog)
    nlinarith
  have hsquare := RecursiveDescriptorDivision.square_log_le V hV
  have hsq : ys.length^2 ≤ 4*C^2*V := by
    calc
      _ ≤ (C*(Nat.log2 V+1))^2 := Nat.pow_le_pow_left hy 2
      _ = C^2*(Nat.log2 V+1)^2 := by ring
      _ ≤ C^2*(4*V) := Nat.mul_le_mul_left _ hsquare
      _ = _ := by ring
  calc
    _ ≤ 32*(ys.length*(4*ys.length+6*ds.length+30))+710 := BinaryDescriptorDivision.cost_le ys ds
    _ = 128*ys.length^2+(192*ds.length+960)*ys.length+710 := by ring
    _ ≤ 128*(4*C^2*V)+(192*ds.length+960)*(2*C*V)+710*V := by
      exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hsq) (Nat.mul_le_mul_left _ hlin))
        (Nat.le_mul_of_pos_right _ hV)
    _ = _ := by ring

def constant (m roles : ℕ) : ℕ :=
  let C := Nat.log2 roles+2
  let D := (RecursiveChildQuotientsConstant.bits m).length+(RecursiveChildQuotientsConstant.bits roles).length
  1024*C^2+(384*D+3840)*C+5*D+1445

theorem cost_le_child_volume {q roles m n d k : ℕ} {root active parent : Descriptor}
    (current : Path q roles m root n active) (parentPath : Path q roles m root d parent)
    (hq : 2 ≤ q) (hr : 0 < roles) (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (hs : Fin 6 → List Bool) (hh : Headers parent hs) :
    RecursiveChildQuotients.cost m roles hs ≤ constant m roles*volume q active := by
  have hpos : 0 < volume q active := lt_of_lt_of_le (pow_pos (by omega : 0 < q) _)
    (current.original_chunks (by omega) hr hv)
  have hlen (i : Fin 6) : (hs i).length ≤ (Nat.log2 roles+2)*(Nat.log2 (volume q active)+1) :=
    RecursiveDescriptorSize.descriptor_length_le_child_log current hq hr hm hw hv (hs i) (hh.2 i)
      (RecursiveHeaderBounds.headers_root_bounded parentPath hq hr hv hs hh i)
  have hb := fixed_divisor_cost (hs 3) (RecursiveChildQuotientsConstant.bits m) (Nat.log2 roles+2) (volume q active) hpos (hlen 3)
  have hr' := fixed_divisor_cost (hs 1) (RecursiveChildQuotientsConstant.bits roles) (Nat.log2 roles+2) (volume q active) hpos (hlen 1)
  have ho := Nat.le_mul_of_pos_right
    (5*((RecursiveChildQuotientsConstant.bits m).length+(RecursiveChildQuotientsConstant.bits roles).length)+25) hpos
  unfold RecursiveChildQuotients.cost constant
  dsimp only
  nlinarith

/-- Real constant initialization and two clean divisions produce canonical
width/row quotients on the exact next constructor bank, with no supplied words. -/
theorem quotients_hoare_linear {q roles m n d k a : ℕ} {root active parent : Descriptor}
    (current : Path q roles m root n active) (parentPath : Path q roles m root d parent)
    (hq : 2 ≤ q) (hr : 0 < roles) (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (hs : Fin 6 → List Bool) (hh : Headers parent hs) :
    ∃ bs rs : List Bool, GrowingCounterData.Canonical bs ∧ GrowingCounterData.Canonical rs ∧
      Counter.value bs = parent.width/m ∧ Counter.value rs = parent.rows/roles ∧
      HoareTime (RecursiveChildQuotients.program (a := a) m roles)
        (fun v => v = RecursiveChildQuotients.input hs)
        (fun v => v = RecursiveChildDimensionsClean.input hs bs rs) (constant m roles*volume q active) := by
  obtain ⟨bs,rs,hbc,hrc,hbv,hrv,hprog⟩ := RecursiveChildQuotients.quotients_hoare (a := a) m roles (by omega) hr hs
  have hwval : Counter.value (hs 3) = parent.width := hh.1 3
  have hrval : Counter.value (hs 1) = parent.rows := hh.1 1
  rw [hwval] at hbv
  rw [hrval] at hrv
  exact ⟨bs,rs,hbc,hrc,hbv,hrv,hprog.consequence (fun _ h => h) (fun _ h => h)
    (cost_le_child_volume current parentPath hq hr hm hw hv hs hh)⟩

end IntegerMultBounds.Machine.RecursiveChildQuotientsBound
