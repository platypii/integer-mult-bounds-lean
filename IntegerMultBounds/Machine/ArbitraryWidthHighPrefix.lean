import IntegerMultBounds.Machine.ArbitraryWidthHighDimensions
import IntegerMultBounds.Machine.ArbitraryWidthHighLayout

/-! Physically fold the three original prefix headers, retaining the inputs
and erasing the intermediate product and all arithmetic workspace. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighPrefix
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet (setTape)

def intermediate (A R : ℕ) := BoundedProductDescriptor.bits A R
def bits (A R C : ℕ) := BoundedProductDescriptor.bits (A*R) C

theorem intermediate_value (A R : ℕ) : Counter.value (intermediate A R) = A*R :=
  BoundedProductDescriptor.bits_value _ _
theorem bits_value (A R C : ℕ) : Counter.value (bits A R C) = A*R*C :=
  BoundedProductDescriptor.bits_value _ _
theorem bits_canonical (A R C : ℕ) : GrowingCounterData.Canonical (bits A R C) :=
  BoundedProductDescriptor.bits_canonical _ _

theorem bits_eq (A R C : ℕ) :
    bits A R C = RecursiveChildQuotientsConstant.bits (A*R*C) :=
  BinaryCanonicalData.value_injective _ _ (bits_canonical A R C)
    (RecursiveChildQuotientsConstant.bits_canonical _) (by
      rw [bits_value,RecursiveChildQuotientsConstant.bits_value])

def bank (hs : Fin 3 → List Bool) (mid out : Option (List Bool)) : Tapes 8 a :=
  ⟨fun i => if i.val < 3 then 1 else if i = 3 then mid.elim 0 (fun _ => 1)
    else if i = 4 then out.elim 0 (fun _ => 1) else 0,
   fun i => if h : i.val < 3 then RadixZeroFill.encodedBinary (hs ⟨i.val,h⟩)
    else if i = 3 then mid.elim (fun _ => blank) RadixZeroFill.encodedBinary
    else if i = 4 then out.elim (fun _ => blank) RadixZeroFill.encodedBinary
    else fun _ => blank⟩
def input (hs : Fin 3 → List Bool) : Tapes 8 a := bank hs none none
def first (A R : ℕ) (hs : Fin 3 → List Bool) : Tapes 8 a :=
  bank hs (some (intermediate A R)) none
def second (A R C : ℕ) (hs : Fin 3 → List Bool) : Tapes 8 a :=
  bank hs (some (intermediate A R)) (some (bits A R C))
def output (A R C : ℕ) (hs : Fin 3 → List Bool) : Tapes 8 a :=
  bank hs none (some (bits A R C))

def firstPlacement : Fin (6+2) ≃ Fin 8 where
  toFun := ![5,3,6,1,7,0,2,4]
  invFun := ![5,3,6,1,7,0,2,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
def secondPlacement : Fin (6+2) ≃ Fin 8 where
  toFun := ![5,4,6,2,7,3,0,1]
  invFun := ![6,7,3,5,1,0,2,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def firstProgram := Placement.placed (BoundedProductDescriptor.program (q := a)) firstPlacement
def secondProgram := Placement.placed (BoundedProductDescriptor.program (q := a)) secondPlacement
def eraseIntermediate : Program 8 4 a := BinaryDescriptorCleanupList.oneProgram 3
def program := seq (seq (firstProgram (a := a)) secondProgram) eraseIntermediate

def cost (A R C : ℕ) := (53*(A*R)+28)+1+(53*(A*R*C)+28)+1+
  (2*(intermediate A R).length+4)

private theorem product_hoare (ws ns : List Bool) (N W : ℕ) (hW : 0 < W)
    (hw : Counter.value ws = W) (hn : Counter.value ns = N)
    (cw : GrowingCounterData.Canonical ws) (cn : GrowingCounterData.Canonical ns) :
    HoareTime (BoundedProductDescriptor.program (q := a))
      (fun z => z = BoundedProductDescriptor.input ws ns)
      (fun z => z = BoundedProductDescriptor.output ws ns N W) (53*(N*W)+28) := by
  have lw := GrowingCounterData.canonical_width ws cw
  have ln := GrowingCounterData.canonical_width ns cn
  rw [hw] at lw
  rw [hn] at ln
  exact BoundedProductDescriptor.construct_hoare ws ns N W N hW hw hn le_rfl
    (lw.trans (Nat.add_le_add_right (Nat.log2_le_self _) 1))
    (ln.trans (Nat.add_le_add_right (Nat.log2_le_self _) 1))

private theorem first_active_input (_A _R _C : ℕ) (hs : Fin 3 → List Bool) :
    Placement.active firstPlacement (input hs : Tapes 8 a) =
      BoundedProductDescriptor.input (hs 1) (hs 0) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
private theorem first_active_output (A R _C : ℕ) (hs : Fin 3 → List Bool) :
    Placement.active firstPlacement (first A R hs : Tapes 8 a) =
      BoundedProductDescriptor.output (hs 1) (hs 0) (A) (R) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
private theorem first_frame (A R _C : ℕ) (hs : Fin 3 → List Bool) :
    Placement.extra firstPlacement (input hs : Tapes 8 a) =
      Placement.extra firstPlacement (first A R hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem second_active_input (A R _C : ℕ) (hs : Fin 3 → List Bool) :
    Placement.active secondPlacement (first A R hs : Tapes 8 a) =
      BoundedProductDescriptor.input (hs 2) (intermediate A R) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
private theorem second_active_output (A R C : ℕ) (hs : Fin 3 → List Bool) :
    Placement.active secondPlacement (second A R C hs : Tapes 8 a) =
      BoundedProductDescriptor.output (hs 2) (intermediate A R) (A*R) (C) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
private theorem second_frame (A R C : ℕ) (hs : Fin 3 → List Bool) :
    Placement.extra secondPlacement (first A R hs : Tapes 8 a) =
      Placement.extra secondPlacement (second A R C hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem first_constructs (A R : ℕ) (hR : 0 < R) (hs : Fin 3 → List Bool)
    (hA : Counter.value (hs 0) = A) (hRv : Counter.value (hs 1) = R)
    (ch : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (firstProgram (a := a)) (fun z => z = input hs)
      (fun z => z = first A R hs) (53*(A*R)+28) := by
  have h := product_hoare (a := a) (hs 1) (hs 0) A R hR hRv hA (ch 1) (ch 0)
  have hp := Placement.hoare_at h firstPlacement (input hs) (first_active_input A R 0 hs)
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨w,rfl,rfl⟩
  rw [Placement.replace,first_frame A R 0 hs,← first_active_output A R 0 hs]
  exact Placement.view _ _

theorem second_constructs (A R C : ℕ) (hC : 0 < C) (hs : Fin 3 → List Bool)
    (hCv : Counter.value (hs 2) = C) (ch : GrowingCounterData.Canonical (hs 2)) :
    HoareTime (secondProgram (a := a)) (fun z => z = first A R hs)
      (fun z => z = second A R C hs) (53*(A*R*C)+28) := by
  have h := product_hoare (a := a) (hs 2) (intermediate A R) (A*R) C hC hCv
    (intermediate_value A R) ch (BoundedProductDescriptor.bits_canonical A R)
  have hp := Placement.hoare_at h secondPlacement (first A R hs) (second_active_input A R C hs)
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨w,rfl,rfl⟩
  rw [Placement.replace,second_frame A R C hs,← second_active_output A R C hs]
  exact Placement.view _ _

private theorem erase_intermediate_bank (A R C : ℕ) (hs : Fin 3 → List Bool) :
    setTape (second (a := a) A R C hs) 3 (fun _ => blank) 0 = output A R C hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem intermediate_cleans (A R C : ℕ) (hs : Fin 3 → List Bool) :
    HoareTime (eraseIntermediate (a := a)) (fun z => z = second A R C hs)
      (fun z => z = output A R C hs) (2*(intermediate A R).length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (3 : Fin 8)
    (second (a := a) A R C hs) (intermediate A R)
    (by change RadixZeroFill.encodedBinary _ = _
        exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm) rfl
  rw [erase_intermediate_bank] at h
  exact h

theorem constructs (A R C : ℕ) (hR : 0 < R) (hC : 0 < C)
    (hs : Fin 3 → List Bool) (hv : ∀ i, Counter.value (hs i) = (![A,R,C] : Fin 3 → ℕ) i)
    (ch : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun z => z = input hs)
      (fun z => z = output A R C hs) (cost A R C) :=
  ((first_constructs A R hR hs (hv 0) (hv 1) ch).seq
    (second_constructs A R C hC hs (hv 2) (ch 2))).seq (intermediate_cleans A R C hs)

theorem constructs_linear (A R C V : ℕ) (hA : 0 < A) (hR : 0 < R) (hC : 0 < C)
    (hV : A*R*C ≤ V) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = (![A,R,C] : Fin 3 → ℕ) i)
    (ch : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun z => z = input hs)
      (fun z => z = output A R C hs) (174*V) := by
  apply (constructs A R C hR hC hs hv ch).consequence (fun _ h => h) (fun _ h => h)
  have hAR : A*R ≤ V := (Nat.le_mul_of_pos_right (A*R) hC).trans hV
  have hp := Nat.mul_pos (Nat.mul_pos hA hR) hC
  have hl := GrowingCounterData.canonical_width (intermediate A R)
    (BoundedProductDescriptor.bits_canonical A R)
  rw [intermediate_value] at hl
  have hlog := Nat.log2_le_self (A*R)
  unfold cost
  omega

def cleanup : Program 8 4 a := BinaryDescriptorCleanupList.oneProgram 4
def cleanupCost (A R C : ℕ) := 2*(bits A R C).length+4
private theorem erase_output_bank (A R C : ℕ) (hs : Fin 3 → List Bool) :
    setTape (output (a := a) A R C hs) 4 (fun _ => blank) 0 = input hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem cleans (A R C : ℕ) (hs : Fin 3 → List Bool) :
    HoareTime (cleanup (a := a)) (fun z => z = output A R C hs)
      (fun z => z = input hs) (cleanupCost A R C) := by
  have h := BinaryDescriptorCleanupList.one_hoare (4 : Fin 8)
    (output (a := a) A R C hs) (bits A R C)
    (by change RadixZeroFill.encodedBinary _ = _
        exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm) rfl
  rw [erase_output_bank] at h
  exact h

theorem cleans_linear (A R C V : ℕ) (hA : 0 < A) (hR : 0 < R) (hC : 0 < C)
    (hV : A*R*C ≤ V) (hs : Fin 3 → List Bool) :
    HoareTime (cleanup (a := a)) (fun z => z = output A R C hs)
      (fun z => z = input hs) (8*V) := by
  apply (cleans A R C hs).consequence (fun _ h => h) (fun _ h => h)
  have hl := GrowingCounterData.canonical_width (bits A R C) (bits_canonical A R C)
  rw [bits_value] at hl
  have hp := Nat.mul_pos (Nat.mul_pos hA hR) hC
  have hlog := Nat.log2_le_self (A*R*C)
  unfold cleanupCost
  omega

theorem output_frame (A R C : ℕ) (hs : Fin 3 → List Bool) (i : Fin 8) (hi : i ≠ 4) :
    (output (a := a) A R C hs).head i = (input (a := a) hs).head i ∧
    (output (a := a) A R C hs).tape i = (input (a := a) hs).tape i := by
  fin_cases i <;> simp_all [output,input,bank]

theorem folded_volume (q A R C e G B : ℕ) :
    RecursiveInterchangeLayout.volume q ⟨A,R,C,e,G,B⟩ =
      RecursiveInterchangeLayout.volume q (ArbitraryWidthHighLayout.originalDescriptor (A*R*C) e G B) := by
  unfold RecursiveInterchangeLayout.volume ArbitraryWidthHighLayout.originalDescriptor
  ring

theorem folded_index (q A R C e G B x row before h middle d after : ℕ) :
    RecursiveInterchangeLayout.index q ⟨A,R,C,e,G,B⟩ x row before h middle d after =
      RecursiveInterchangeLayout.index q
        (ArbitraryWidthHighLayout.originalDescriptor (A*R*C) e G B)
        ((x*R+row)*C+before) 0 0 h middle d after := by
  unfold RecursiveInterchangeLayout.index ArbitraryWidthHighLayout.originalDescriptor
  ring

end
end IntegerMultBounds.Machine.ArbitraryWidthHighPrefix
