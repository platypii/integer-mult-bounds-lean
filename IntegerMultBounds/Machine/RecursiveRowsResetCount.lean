import IntegerMultBounds.Machine.RecursiveRowsConstruct

/-! An actual final product provides the erase/reset length for either the
common source or all role sources. The count is never supplied by the caller. -/
namespace IntegerMultBounds.Machine.RecursiveRowsResetCount
open RecursiveInterchangeLayout (Descriptor volume role)
variable {q : ℕ} (hq : 2 ≤ q)
noncomputable section

inductive Target | common | roles

def factor (c : ℕ) (v : Descriptor) : Target → ℕ
  | .common => v.beforeRows*v.rows
  | .roles => v.beforeRows*(v.rows/c)

def bits (c : ℕ) (v : Descriptor) (target : Target) :=
  DimensionProductDescriptor.bits (factor c v target) (RecursiveInterchangeRows.rowLength q v)

def count (c : ℕ) (v : Descriptor) : Target → ℕ
  | .common => volume q v
  | .roles => volume q (role v c)

theorem bits_value (c : ℕ) (v : Descriptor) (target : Target) :
    Counter.value (bits (q := q) c v target) = count (q := q) c v target := by
  cases target <;> simp only [bits,DimensionProductDescriptor.bits_value,factor,count,
    volume,role,RecursiveInterchangeRows.rowLength] <;> ring

def output (c : ℕ) (hs : Fin 6 → List Bool) (v : Descriptor) (rs : List Bool) (target : Target) :=
  SharedPlacementAlphabet.setTape (RecursiveRowsDimensions.output hq c hs v rs) 20
    (RadixZeroFill.encodedBinary (bits (q := q) c v target)) 1

def commonPlacement : Fin (6+32) ≃ Fin 38 where
  toFun := ![0,20,1,18,2,11,3,4,5,6,7,8,9,10,12,13,14,15,16,17,19,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  invFun := ![0,2,4,6,7,8,9,10,11,12,13,5,14,15,16,17,18,19,3,20,1,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def rolesPlacement : Fin (6+32) ≃ Fin 38 where
  toFun := ![0,20,1,18,2,19,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  invFun := ![0,2,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,3,5,1,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def placement : Target → Fin (6+32) ≃ Fin 38 | .common => commonPlacement | .roles => rolesPlacement

def program (target : Target) : Program 38 40 q :=
  Placement.placed DimensionProductDescriptor.program (placement target)

def factorBits (c : ℕ) (v : Descriptor) : Target → List Bool
  | .common => RecursiveDimensionBank.arBits v
  | .roles => RecursiveRowsDimensions.groupBits c v

theorem constructs_hoare (c : ℕ) (hs : Fin 6 → List Bool) (v : Descriptor) (rs : List Bool)
    (hp : v.Positive) (target : Target) :
    HoareTime (program (q := q) target) (fun w => w = RecursiveRowsDimensions.output hq c hs v rs)
      (fun w => w = output hq c hs v rs target) (53*count (q := q) c v target+28) := by
  have hrow : 0 < RecursiveInterchangeRows.rowLength q v := by
    have hQ : 0 < q^v.width := pow_pos (by omega) _
    rcases hp with ⟨ha,hr,hb,hc,he⟩
    unfold RecursiveInterchangeRows.rowLength
    positivity
  have hb := (RecursiveRowsDimensions.words_value (q := q) c v).1
  have hf : Counter.value (factorBits c v target) = factor c v target := by
    cases target <;> exact DimensionProductDescriptor.bits_value _ _
  have hfc : GrowingCounterData.Canonical (factorBits c v target) := by
    cases target <;> exact DimensionProductDescriptor.bits_canonical _ _
  have hh := DimensionProductDescriptor.construct_hoare (q := q) (RecursiveRowsDimensions.rowBits (q := q) v)
    (factorBits c v target) (factor c v target) (RecursiveInterchangeRows.rowLength q v)
    hrow hb hf (DimensionProductDescriptor.bits_canonical _ _) hfc
  have he : factor c v target*RecursiveInterchangeRows.rowLength q v = count (q := q) c v target := by
    simpa only [bits,DimensionProductDescriptor.bits_value] using bits_value (q := q) c v target
  rw [he] at hh
  have hi : Placement.active (placement target) (RecursiveRowsDimensions.output hq c hs v rs) =
      DimensionProductDescriptor.input (RecursiveRowsDimensions.rowBits (q := q) v) (factorBits c v target) := by
    cases target <;> apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have ho : Placement.active (placement target) (output hq c hs v rs target) =
      DimensionProductDescriptor.output (RecursiveRowsDimensions.rowBits (q := q) v) (factorBits c v target)
        (factor c v target) (RecursiveInterchangeRows.rowLength q v) := by
    cases target <;> apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hframe : Placement.extra (placement target) (RecursiveRowsDimensions.output hq c hs v rs) =
      Placement.extra (placement target) (output hq c hs v rs target) := by
    cases target <;> apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply (Placement.hoare_at hh (placement target) _ hi).consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  rw [Placement.replace,hframe,← ho]
  exact Placement.view _ _

theorem count_le (c : ℕ) (v : Descriptor) (target : Target) : count (q := q) c v target ≤ volume q v := by
  cases target
  · rfl
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.div_le_self v.rows c))))))

theorem ready (c : ℕ) (hs : Fin 6 → List Bool) (v : Descriptor) (rs : List Bool) (target : Target) :
    (output hq c hs v rs target).head 20 = 1 ∧
    (output hq c hs v rs target).tape 20 = RadixZeroFill.encodedBinary (bits (q := q) c v target) := by
  simp [output,SharedPlacementAlphabet.setTape]

end
end IntegerMultBounds.Machine.RecursiveRowsResetCount
