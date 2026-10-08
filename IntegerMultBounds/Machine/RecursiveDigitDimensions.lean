import IntegerMultBounds.Machine.RecursiveScalingDimensions

/-! Physical width-one base dimensions. The H-scaling bank already constructs
Q, O=A*rows*beforeH and C*Q*E. One additional actual product constructs O*C.
Only the original six headers are supplied; every other tape starts blank. -/
namespace IntegerMultBounds.Machine.RecursiveDigitDimensions
open RecursiveInterchangeLayout (Descriptor volume)
variable {q : ℕ} (hq : 2 ≤ q)

def ocBits (v : Descriptor) := DimensionProductDescriptor.bits (v.beforeRows*v.rows*v.beforeH) v.between

def tailBank (xs : Option (List Bool)) : Tapes 1 q :=
  ⟨fun _ => RecursiveDimensionBank.head xs,fun _ => RecursiveDimensionBank.tape xs⟩

def input (hs : Fin 6 → List Bool) : Tapes 17 q :=
  (RecursiveScalingDimensions.input hs).append (tailBank none)

def output (hs : Fin 6 → List Bool) (v : Descriptor) : Tapes 17 q :=
  (RecursiveScalingDimensions.output hq hs v .h).append (tailBank (some (ocBits v)))

def placement : Fin (6+11) ≃ Fin 17 where
  toFun := ![0,16,1,7,2,11,3,4,5,6,8,9,10,12,13,14,15]
  invFun := ![0,2,4,6,7,8,9,3,10,11,12,5,13,14,15,16,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def productProgram : Program 17 40 q := Placement.placed DimensionProductDescriptor.program placement

def program := seq (extend (RecursiveScalingDimensions.program hq .h) 1) productProgram

private theorem product_frame (v : Tapes 16 q) (xs : List Bool) :
    Placement.extra placement (v.append (tailBank none)) =
      Placement.extra placement (v.append (tailBank (some xs))) := by
  unfold Placement.extra placement
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd] <;> norm_num [Tapes.append,Fin.addCases]

theorem product_hoare (v : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (productProgram (q := q))
      (fun w => w = (RecursiveScalingDimensions.output hq hs v .h).append (tailBank none))
      (fun w => w = output hq hs v) (53*((v.beforeRows*v.rows*v.beforeH)*v.between)+28) := by
  have hh := DimensionProductDescriptor.construct_hoare (q := q) (hs 4) (RecursiveDimensionBank.arbBits v)
    (v.beforeRows*v.rows*v.beforeH) v.between hvpos.2.2.2.1 (hv.1 4)
    (DimensionProductDescriptor.bits_value _ _) (hv.2 4) (DimensionProductDescriptor.bits_canonical _ _)
  have ha : Placement.active placement
      ((RecursiveScalingDimensions.output hq hs v .h).append (tailBank (q := q) none)) =
      DimensionProductDescriptor.input (hs 4) (RecursiveDimensionBank.arbBits v) := by
    unfold Placement.active placement RecursiveScalingDimensions.output RecursiveScalingDimensions.bank
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hb : Placement.active placement (output hq hs v) =
      DimensionProductDescriptor.output (hs 4) (RecursiveDimensionBank.arbBits v)
        (v.beforeRows*v.rows*v.beforeH) v.between := by
    unfold Placement.active placement output RecursiveScalingDimensions.output RecursiveScalingDimensions.bank
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hf := Placement.hoare_at hh placement _ ha
  apply hf.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  rw [Placement.replace,product_frame,← hb]
  exact Placement.view _ _

theorem constructs_hoare (v : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program hq) (fun w => w = input hs) (fun w => w = output hq hs v)
      (417*volume q v+174) := by
  have hd := hoare_extend_eq (RecursiveScalingDimensions.constructs_hoare hq v hs .h hv hvpos)
    (tailBank (q := q) none)
  have hh := hd.seq (product_hoare hq v hs hv hvpos)
  apply hh.consequence (fun _ h => h) (fun _ h => h) ?_
  have hOC : (v.beforeRows*v.rows*v.beforeH)*v.between ≤ volume q v := by
    have hQ : 0 < q^v.width := pow_pos (by omega) _
    have hp := Nat.le_mul_of_pos_right ((v.beforeRows*v.rows*v.beforeH)*v.between)
      (by have := hvpos.2.2.2.2; positivity : 0 < q^v.width*q^v.width*v.afterD)
    convert hp using 1
    simp only [volume]
    ring
  omega

def words (v : Descriptor) (hs : Fin 6 → List Bool) : Fin 4 → List Bool :=
  ![RecursiveScalingDimensions.cqeBits (q := q) v,RecursiveDimensionBank.arbBits v,hs 5,ocBits v]

def sourceSlots : Fin 4 → Fin 17 := ![14,11,8,16]

theorem ready (v : Descriptor) (hs : Fin 6 → List Bool) (j : Fin 4) :
    (output hq hs v).head (sourceSlots j) = 1 ∧
    (output hq hs v).tape (sourceSlots j) = RadixZeroFill.encodedBinary (words (q := q) v hs j) := by
  fin_cases j <;> exact ⟨rfl,rfl⟩


def values (v : Descriptor) : Fin 4 → ℕ :=
  ![v.between*(q*v.afterD),v.beforeRows*v.rows*v.beforeH,v.afterD,(v.beforeRows*v.rows*v.beforeH)*v.between]

theorem words_values (v : Descriptor) (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (hw : v.width = 1) (j : Fin 4) : Counter.value (words (q := q) v hs j) = values (q := q) v j := by
  fin_cases j
  · simp [words,values,RecursiveScalingDimensions.cqeBits,DimensionProductDescriptor.bits_value,hw]
  · exact DimensionProductDescriptor.bits_value _ _
  · exact hv.1 5
  · exact DimensionProductDescriptor.bits_value _ _

theorem words_canonical (v : Descriptor) (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (j : Fin 4) : GrowingCounterData.Canonical (words (q := q) v hs j) := by
  fin_cases j
  · exact DimensionProductDescriptor.bits_canonical _ _
  · exact DimensionProductDescriptor.bits_canonical _ _
  · exact hv.2 5
  · exact DimensionProductDescriptor.bits_canonical _ _

theorem words_length (hq : 2 ≤ q) (v : Descriptor) (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (hvpos : v.Positive) (hw : v.width = 1) (j : Fin 4) :
    (words (q := q) v hs j).length ≤ 2*volume q v := by
  have hQ : 0 < q := by omega
  have hO : 0 < v.beforeRows*v.rows*v.beforeH :=
    Nat.mul_pos (Nat.mul_pos hvpos.1 hvpos.2.1) hvpos.2.2.1
  have hC := hvpos.2.2.2.1
  have hE := hvpos.2.2.2.2
  have hB : 0 < v.between*(q*v.afterD) := Nat.mul_pos hC (Nat.mul_pos hQ hE)
  have hvol : volume q v = (v.beforeRows*v.rows*v.beforeH)*(q*(v.between*(q*v.afterD))) := by
    simp only [volume,hw,pow_one]
    ring
  have hV : 0 < volume q v := by rw [hvol]; positivity
  have hb : v.between*(q*v.afterD) ≤ volume q v := by
    rw [hvol]
    exact (Nat.le_mul_of_pos_left _ hQ).trans (Nat.le_mul_of_pos_left _ hO)
  have ho : v.beforeRows*v.rows*v.beforeH ≤ volume q v := by
    rw [hvol]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hQ hB)
  have he : v.afterD ≤ volume q v :=
    ((Nat.le_mul_of_pos_left _ hQ).trans (Nat.le_mul_of_pos_left _ hC)).trans hb
  have hoc : (v.beforeRows*v.rows*v.beforeH)*v.between ≤ volume q v := by
    have hh := Nat.le_mul_of_pos_right ((v.beforeRows*v.rows*v.beforeH)*v.between)
      (Nat.mul_pos hQ (Nat.mul_pos hQ hE))
    convert hh using 1
    rw [hvol]
    ring
  have hn : Counter.value (words (q := q) v hs j) ≤ volume q v := by
    rw [words_values v hs hv hw j]
    fin_cases j <;> first | exact hb | exact ho | exact he | exact hoc
  have hwidth := GrowingCounterData.canonical_width _ (words_canonical (q := q) v hs hv j)
  have hlog := Nat.log2_le_self (Counter.value (words (q := q) v hs j))
  omega

def headerSlot (j : Fin 6) : Fin 17 := Fin.castAdd 1 (Fin.castAdd 3 (Fin.castAdd 4 (Fin.natAdd 3 j)))

theorem input_header (hs : Fin 6 → List Bool) (j : Fin 6) :
    (input (q := q) hs).head (headerSlot j) = 1 ∧
    (input (q := q) hs).tape (headerSlot j) = RadixZeroFill.encodedBinary (hs j) := by
  unfold input RecursiveScalingDimensions.input RecursiveScalingDimensions.bank headerSlot
  simp only [Tapes.append,Fin.addCases_left]
  exact RecursiveDimensionBank.headers_preserved hs _ j

theorem headers_preserved (hs : Fin 6 → List Bool) (v : Descriptor) (j : Fin 6) :
    (output hq hs v).head (headerSlot j) = 1 ∧
    (output hq hs v).tape (headerSlot j) = RadixZeroFill.encodedBinary (hs j) := by
  unfold output RecursiveScalingDimensions.output RecursiveScalingDimensions.bank headerSlot
  simp only [Tapes.append,Fin.addCases_left]
  exact RecursiveDimensionBank.headers_preserved hs _ j

theorem input_blank (hs : Fin 6 → List Bool) (i : Fin 17) (hi : ¬ (3 ≤ i.val ∧ i.val < 9)) :
    (input (q := q) hs).head i = 0 ∧ (input (q := q) hs).tape i = fun _ => blank := by
  fin_cases i <;> first | exact ⟨rfl,rfl⟩ | (exfalso; exact hi (by decide))

end IntegerMultBounds.Machine.RecursiveDigitDimensions
