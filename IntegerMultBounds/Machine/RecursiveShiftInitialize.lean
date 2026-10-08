import IntegerMultBounds.Machine.RecursiveShiftInstall

/-! Full heterogeneous-shift setup from six canonical layout headers and the
sole payload. All dimension outputs and shift workspace are initially blank;
original headers remain present at the exact prepared endpoint. -/
namespace IntegerMultBounds.Machine.RecursiveShiftInitialize
open RecursiveInterchangeLayout (Descriptor volume)
variable {q : ℕ} [Fact q.Prime]
noncomputable section

def dimensions (v : Descriptor) (hs : Fin 6 → List Bool) : Fin 5 → List Bool :=
  ![hs 5,RecursiveDimensionBank.qBits (Fact.out : q.Prime).two_le v,hs 4,
    RecursiveDimensionBank.nBits (q := q) v,hs 3]

def input (hs : Fin 6 → List Bool) (source : ℤ → Fin 4) : Tapes 34 q :=
  (RecursiveDimensionBank.bank (q := q) hs RecursiveDimensionBank.ds0).append (RecursiveShiftInstall.blankLocal source)

def output (v : Descriptor) (hs : Fin 6 → List Bool) (source : ℤ → Fin 4) : Tapes 34 q :=
  (RecursiveDimensionBank.bank (q := q) hs (RecursiveDimensionBank.ds4 (Fact.out : q.Prime).two_le v)).append
    (RepeatedControlBootstrap.output source (fun _ => blank) 0 0 (dimensions (q := q) v hs 0) (dimensions (q := q) v hs 1)
      (dimensions (q := q) v hs 2) (dimensions (q := q) v hs 3) (dimensions (q := q) v hs 4) v.width)

def program := seq (seq (extend (RecursiveDimensionBank.program (Fact.out : q.Prime).two_le) 21)
  (RecursiveShiftInstall.program q)) (Placement.placed (RepeatedControlBootstrap.program (radix := q)) finAddFlip)

private theorem left_frame {n s q a k : ℕ} {M : Program n s a} {x y : Tapes n a}
    (h : HoareTime M (fun v => v = x) (fun v => v = y) k) (v : Tapes q a) :
    HoareTime (Placement.placed M (finAddFlip : Fin (n+q) ≃ Fin (q+n)))
      (fun w => w = v.append x) (fun w => w = v.append y) k := by
  have he (z : Tapes n a) : Placement.combine finAddFlip z v = v.append z := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
      simp [Tapes.append,finAddFlip]
  have hh := Placement.hoare_at h finAddFlip (Placement.combine finAddFlip x v)
    (Placement.active_combine _ _ _)
  apply hh.consequence (fun w hw => hw.trans (he x).symm) _ le_rfl
  rintro w ⟨z,hz,rfl⟩
  subst z
  simpa only [Placement.replace,Placement.extra_combine] using he y

private theorem dimensions_ready (v : Descriptor) (hs : Fin 6 → List Bool) (i : Fin 5) :
    (RecursiveDimensionBank.bank (q := q) hs (RecursiveDimensionBank.ds4 (Fact.out : q.Prime).two_le v)).head
        (RecursiveShiftInstall.sourceSlots i) = 1 ∧
    (RecursiveDimensionBank.bank (q := q) hs (RecursiveDimensionBank.ds4 (Fact.out : q.Prime).two_le v)).tape
        (RecursiveShiftInstall.sourceSlots i) = RadixZeroFill.encodedBinary (dimensions (q := q) v hs i) := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

/-- Exact setup cost including all five descriptor copies and all joins. -/
theorem construct_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (source : ℤ → Fin 4)
    (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program (q := q)) (fun w => w = input hs source) (fun w => w = output (q := q) v hs source)
      (258*volume q v+15*v.width+
        BinaryDescriptorInstallMarkedList.cost RecursiveShiftInstall.instructions (RecursiveShiftInstall.words (dimensions (q := q) v hs))+119) := by
  have hd := hoare_extend_eq (RecursiveDimensionBank.construct_hoare (Fact.out : q.Prime).two_le v hs hv hvpos)
    (RecursiveShiftInstall.blankLocal (q := q) source)
  have hi := RecursiveShiftInstall.installs_hoare
    (RecursiveDimensionBank.bank (q := q) hs (RecursiveDimensionBank.ds4 (Fact.out : q.Prime).two_le v)) source
    (dimensions (q := q) v hs) (dimensions_ready (q := q) v hs)
  have hb := RepeatedControlBootstrap.construct_hoare (radix := q) source (fun _ => blank) 0 0
    (dimensions (q := q) v hs 0) (dimensions (q := q) v hs 1) (dimensions (q := q) v hs 2) (dimensions (q := q) v hs 3) (dimensions (q := q) v hs 4)
    v.width (hv.1 3) (hv.2 3)
  have hh := (hd.seq hi).seq (left_frame hb
    (RecursiveDimensionBank.bank (q := q) hs (RecursiveDimensionBank.ds4 (Fact.out : q.Prime).two_le v)))
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

private theorem volume_bounds (v : Descriptor) (hv : v.Positive) :
    q^v.width ≤ volume q v ∧ v.beforeRows*v.rows*v.beforeH*q^v.width ≤ volume q v ∧
      v.between ≤ volume q v ∧ v.afterD ≤ volume q v ∧ v.width ≤ volume q v := by
  rcases hv with ⟨hA,hR,hB,hC,hE⟩
  have hQ : 0 < q^v.width := pow_pos (Fact.out : q.Prime).pos _
  have hP : 0 < v.beforeRows*v.rows*v.beforeH := Nat.mul_pos (Nat.mul_pos hA hR) hB
  have hN : 0 < v.beforeRows*v.rows*v.beforeH*q^v.width := Nat.mul_pos hP hQ
  have hE' : v.afterD ≤ volume q v := by
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos hN hC) hQ)
  have hC' : v.between ≤ volume q v := by
    have h1 := Nat.le_mul_of_pos_right v.between (Nat.mul_pos hQ hE)
    have h2 := Nat.le_mul_of_pos_left (v.between*(q^v.width*v.afterD)) hN
    have he : v.beforeRows*v.rows*v.beforeH*q^v.width*(v.between*(q^v.width*v.afterD)) = volume q v := by
      simp only [volume]; ring
    rw [he] at h2
    exact h1.trans h2
  have hn : v.beforeRows*v.rows*v.beforeH*q^v.width ≤ volume q v := by
    have hh := Nat.le_mul_of_pos_right (v.beforeRows*v.rows*v.beforeH*q^v.width) (Nat.mul_pos hC (Nat.mul_pos hQ hE))
    convert hh using 1
    simp only [volume]
    ring
  have hq := (Nat.le_mul_of_pos_left (q^v.width) hP).trans hn
  exact ⟨hq,hn,hC',hE',(RadixToBinaryData.width_le_power (Fact.out : q.Prime).two_le v.width).trans hq⟩

theorem dimension_lengths (v : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) (i : Fin 5) :
    (dimensions (q := q) v hs i).length ≤ volume q v+1 := by
  have bound (xs : List Bool) (hc : GrowingCounterData.Canonical xs) (hval : Counter.value xs ≤ volume q v) :
      xs.length ≤ volume q v+1 := by
    have hw := GrowingCounterData.canonical_width xs hc
    have hl := Nat.log2_le_self (Counter.value xs)
    omega
  obtain ⟨hQ,hN,hC,hE,hW⟩ := volume_bounds (q := q) v hvpos
  fin_cases i
  · exact bound _ (hv.2 5) (by simpa [dimensions,hv.1 5,RecursiveDimensionBank.values] using hE)
  · exact bound _ (RadixPowerDescriptor.bits_canonical _ _) (by simpa [dimensions,RecursiveDimensionBank.qBits] using hQ)
  · exact bound _ (hv.2 4) (by simpa [dimensions,hv.1 4,RecursiveDimensionBank.values] using hC)
  · exact bound _ (DimensionProductDescriptor.bits_canonical _ _) (by simpa [dimensions,RecursiveDimensionBank.nBits,DimensionProductDescriptor.bits_value] using hN)
  · exact bound _ (hv.2 3) (by simpa [dimensions,hv.1 3,RecursiveDimensionBank.values] using hW)

theorem construct_hoare_linear (v : Descriptor) (hs : Fin 6 → List Bool) (source : ℤ → Fin 4)
    (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program (q := q)) (fun w => w = input hs source) (fun w => w = output (q := q) v hs source)
      (283*volume q v+159) := by
  have hh := construct_hoare (q := q) v hs source hv hvpos
  have hc := RecursiveShiftInstall.cost_bound (dimensions (q := q) v hs) (volume q v+1)
    (dimension_lengths v hs hv hvpos)
  have hw := (volume_bounds (q := q) v hvpos).2.2.2.2
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.RecursiveShiftInitialize
