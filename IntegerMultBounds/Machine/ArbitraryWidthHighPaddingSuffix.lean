import IntegerMultBounds.Machine.ArbitraryWidthHighDimensions
import IntegerMultBounds.Machine.ArbitraryWidthHighLayout

/-! The joined-row suffix is physically multiplied from the two retained
movement dimensions. Its output and all cleanup costs are linear in that row. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighPaddingSuffix
noncomputable section
variable {a : ℕ}
open RecursiveInterchangeLayout (volume)
open SharedPlacementAlphabet (setTape)

def rowLength (q e r G B : ℕ) := G*B*q^(2*(e-r))
def bits (q e r G B : ℕ) := BoundedProductDescriptor.bits (B*q^(e-r)) (G*q^(e-r))

theorem bits_value (q e r G B : ℕ) : Counter.value (bits q e r G B) = rowLength q e r G B := by
  rw [bits,BoundedProductDescriptor.bits_value]
  unfold rowLength
  rw [show q^(2*(e-r)) = q^(e-r)*q^(e-r) by rw [← pow_add]; congr 1; omega]
  ring

theorem bits_canonical (q e r G B : ℕ) : GrowingCounterData.Canonical (bits q e r G B) :=
  BoundedProductDescriptor.bits_canonical _ _

theorem bits_eq (q e r G B : ℕ) :
    bits q e r G B = RecursiveChildQuotientsConstant.bits (rowLength q e r G B) :=
  BinaryCanonicalData.value_injective _ _ (bits_canonical q e r G B)
    (RecursiveChildQuotientsConstant.bits_canonical _) (by
      rw [bits_value,RecursiveChildQuotientsConstant.bits_value])

theorem rowLength_positive (q e r G B : ℕ) (hq : 2 ≤ q) (hG : 0 < G) (hB : 0 < B) :
    0 < rowLength q e r G B := Nat.mul_pos (Nat.mul_pos hG hB) (pow_pos (by omega) _)

theorem joined_rowLength (q P e r G B : ℕ) :
    RecursiveInterchangeRows.rowLength q (ArbitraryWidthHighLayout.joinedDescriptor q P e r G B) =
      rowLength q e r G B := by
  unfold RecursiveInterchangeRows.rowLength ArbitraryWidthHighLayout.joinedDescriptor rowLength
  rw [show q^(2*(e-r)) = q^(e-r)*q^(e-r) by rw [← pow_add]; congr 1; omega]
  ring

def localProgram := BoundedProductDescriptor.program (q := a)
def localCost (q e r G B : ℕ) := 53*rowLength q e r G B+28

theorem local_constructs (q e r G B : ℕ) (hq : 2 ≤ q) (hG : 0 < G) (_hB : 0 < B)
    (gs bs : List Bool) (hg : Counter.value gs = G*q^(e-r)) (hb : Counter.value bs = B*q^(e-r))
    (cg : GrowingCounterData.Canonical gs) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (localProgram (a := a)) (fun z => z = BoundedProductDescriptor.input gs bs)
      (fun z => z = BoundedProductDescriptor.output gs bs (B*q^(e-r)) (G*q^(e-r)))
      (localCost q e r G B) := by
  have hlG := GrowingCounterData.canonical_width gs cg
  have hlB := GrowingCounterData.canonical_width bs cb
  rw [hg] at hlG
  rw [hb] at hlB
  have h := BoundedProductDescriptor.construct_hoare (q := a) gs bs (B*q^(e-r)) (G*q^(e-r))
    (B*q^(e-r)) (Nat.mul_pos hG (pow_pos (by omega) _)) hg hb le_rfl
    (hlG.trans (Nat.add_le_add_right (Nat.log2_le_self _) 1))
    (hlB.trans (Nat.add_le_add_right (Nat.log2_le_self _) 1))
  have he : (B*q^(e-r))*(G*q^(e-r)) = rowLength q e r G B := by
    unfold rowLength
    rw [show q^(2*(e-r)) = q^(e-r)*q^(e-r) by rw [← pow_add]; congr 1; omega]
    ring
  rw [he] at h
  exact h

theorem local_linear (q e r G B : ℕ) (hq : 2 ≤ q) (hG : 0 < G) (hB : 0 < B)
    (gs bs : List Bool) (hg : Counter.value gs = G*q^(e-r)) (hb : Counter.value bs = B*q^(e-r))
    (cg : GrowingCounterData.Canonical gs) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (localProgram (a := a)) (fun z => z = BoundedProductDescriptor.input gs bs)
      (fun z => z = BoundedProductDescriptor.output gs bs (B*q^(e-r)) (G*q^(e-r)))
      (81*rowLength q e r G B) := by
  exact (local_constructs q e r G B hq hG hB gs bs hg hb cg cb).consequence
    (fun _ h => h) (fun _ h => h) (by
      have h := rowLength_positive q e r G B hq hG hB
      unfold localCost
      omega)

def placement : Fin (6+11) ≃ Fin 17 where
  toFun := ![11,12,13,9,14,10,0,1,2,3,4,5,6,7,8,15,16]
  invFun := ![6,7,8,9,10,11,12,13,14,3,5,0,1,2,4,15,16]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def program := Placement.placed (localProgram (a := a)) placement

def output (q P e r G B : ℕ) (hs : Fin 5 → List Bool) : Tapes 17 a :=
  setTape (ArbitraryWidthHighDimensions.output q P G B e r hs) 12
    (RadixZeroFill.encodedBinary (bits q e r G B)) 1

theorem output_frame (q P e r G B : ℕ) (hs : Fin 5 → List Bool) (i : Fin 17)
    (hi : i ≠ 12) :
    (output (a := a) q P e r G B hs).head i =
      (ArbitraryWidthHighDimensions.output (a := a) q P G B e r hs).head i ∧
    (output (a := a) q P e r G B hs).tape i =
      (ArbitraryWidthHighDimensions.output (a := a) q P G B e r hs).tape i := by
  simp [output,setTape,hi]

private theorem active_input (q P e r G B : ℕ) (hs : Fin 5 → List Bool) :
    Placement.active placement (ArbitraryWidthHighDimensions.output (a := a) q P G B e r hs) =
      BoundedProductDescriptor.input (ArbitraryWidthHighDimensions.words q P G B e r 4)
        (ArbitraryWidthHighDimensions.words q P G B e r 5) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem active_output (q P e r G B : ℕ) (hs : Fin 5 → List Bool) :
    Placement.active placement (output (a := a) q P e r G B hs) =
      BoundedProductDescriptor.output (ArbitraryWidthHighDimensions.words q P G B e r 4)
        (ArbitraryWidthHighDimensions.words q P G B e r 5) (B*q^(e-r)) (G*q^(e-r)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem extra_frame (q P e r G B : ℕ) (hs : Fin 5 → List Bool) :
    Placement.extra placement (ArbitraryWidthHighDimensions.output (a := a) q P G B e r hs) =
      Placement.extra placement (output q P e r G B hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem constructs (q P e r G B : ℕ) (hq : 2 ≤ q) (hG : 0 < G) (hB : 0 < B)
    (hs : Fin 5 → List Bool) :
    HoareTime (program (a := a))
      (fun z => z = ArbitraryWidthHighDimensions.output q P G B e r hs)
      (fun z => z = output q P e r G B hs) (localCost q e r G B) := by
  have h := local_constructs (a := a) q e r G B hq hG hB
    (ArbitraryWidthHighDimensions.words q P G B e r 4)
    (ArbitraryWidthHighDimensions.words q P G B e r 5)
    (ArbitraryWidthHighDimensions.words_value _ _ _ _ _ _ 4)
    (ArbitraryWidthHighDimensions.words_value _ _ _ _ _ _ 5)
    (ArbitraryWidthHighDimensions.words_canonical _ _ _ _ _ _ 4)
    (ArbitraryWidthHighDimensions.words_canonical _ _ _ _ _ _ 5)
  have hp := Placement.hoare_at h placement
    (ArbitraryWidthHighDimensions.output q P G B e r hs) (active_input _ _ _ _ _ _ _)
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨w,rfl,rfl⟩
  rw [Placement.replace,extra_frame,← active_output]
  exact Placement.view _ _

theorem constructs_linear (q P e r G B : ℕ) (hq : 2 ≤ q) (hG : 0 < G) (hB : 0 < B)
    (hs : Fin 5 → List Bool) :
    HoareTime (program (a := a))
      (fun z => z = ArbitraryWidthHighDimensions.output q P G B e r hs)
      (fun z => z = output q P e r G B hs) (81*rowLength q e r G B) :=
  (constructs q P e r G B hq hG hB hs).consequence (fun _ h => h) (fun _ h => h) (by
    have h := rowLength_positive q e r G B hq hG hB
    unfold localCost
    omega)


def cleanup : Program 17 4 a := BinaryDescriptorCleanupList.oneProgram 12

def cleanupCost (q e r G B : ℕ) := 2*(bits q e r G B).length+4

private theorem cleaned_output (q P e r G B : ℕ) (hs : Fin 5 → List Bool) :
    setTape (output (a := a) q P e r G B hs) 12 (fun _ => blank) 0 =
      ArbitraryWidthHighDimensions.output q P G B e r hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem cleans (q P e r G B : ℕ) (hs : Fin 5 → List Bool) :
    HoareTime (cleanup (a := a)) (fun z => z = output q P e r G B hs)
      (fun z => z = ArbitraryWidthHighDimensions.output q P G B e r hs)
      (cleanupCost q e r G B) := by
  have h := BinaryDescriptorCleanupList.one_hoare (12 : Fin 17)
    (output (a := a) q P e r G B hs) (bits q e r G B)
    (by change RadixZeroFill.encodedBinary _ = _
        exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm) rfl
  rw [cleaned_output] at h
  exact h

theorem cleans_linear (q P e r G B : ℕ) (hq : 2 ≤ q) (hG : 0 < G) (hB : 0 < B)
    (hs : Fin 5 → List Bool) :
    HoareTime (cleanup (a := a)) (fun z => z = output q P e r G B hs)
      (fun z => z = ArbitraryWidthHighDimensions.output q P G B e r hs)
      (8*rowLength q e r G B) := by
  apply (cleans q P e r G B hs).consequence (fun _ h => h) (fun _ h => h)
  have hl := GrowingCounterData.canonical_width (bits q e r G B) (bits_canonical q e r G B)
  rw [bits_value] at hl
  have hlog := Nat.log2_le_self (rowLength q e r G B)
  have hp := rowLength_positive q e r G B hq hG hB
  unfold cleanupCost
  omega

theorem original_volume (q P e G B : ℕ) :
    volume q (ArbitraryWidthHighLayout.originalDescriptor P e G B) =
      ArbitraryWidthHighDimensions.dataVolume q P G B e := by
  unfold volume ArbitraryWidthHighLayout.originalDescriptor ArbitraryWidthHighDimensions.dataVolume
  rw [show q^(2*e) = q^e*q^e by rw [← pow_add]; congr 1; omega]
  ring

theorem suffix_le_parent (q P e r G B : ℕ) (hq : 2 ≤ q) (hr : r ≤ e)
    (hP : 0 < P) :
    rowLength q e r G B ≤ volume q (ArbitraryWidthHighLayout.originalDescriptor P e G B) := by
  have hpow : q^(2*(e-r)) ≤ q^(2*e) :=
    Nat.pow_le_pow_right (by omega : 0 < q) (by omega)
  have hout : G*B ≤ P*G*B := by
    convert Nat.le_mul_of_pos_left (G*B) hP using 1; ring
  rw [original_volume]
  exact Nat.mul_le_mul hout hpow

theorem padded_volume (q P e r G B R : ℕ) :
    volume q (RecursiveRowPadding.withRows (ArbitraryWidthHighLayout.joinedDescriptor q P e r G B) R) =
      P*R*rowLength q e r G B := by
  unfold volume RecursiveRowPadding.withRows ArbitraryWidthHighLayout.joinedDescriptor rowLength
  rw [show q^(2*(e-r)) = q^(e-r)*q^(e-r) by rw [← pow_add]; congr 1; omega]
  ring

theorem suffix_le_padded (q P e r G B R : ℕ) (hP : 0 < P) (hR : 0 < R) :
    rowLength q e r G B ≤
      volume q (RecursiveRowPadding.withRows (ArbitraryWidthHighLayout.joinedDescriptor q P e r G B) R) := by
  rw [padded_volume]
  exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hP hR)


end
end IntegerMultBounds.Machine.ArbitraryWidthHighPaddingSuffix
