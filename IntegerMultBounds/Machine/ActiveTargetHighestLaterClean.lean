import IntegerMultBounds.Machine.ActiveTargetHighestLaterValue

/-! Exact reusable bank interface for the earlier highest-bit machine, needed
between the two physical interchanges in the later-source construction. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLaterClean
noncomputable section
open ActiveTargetHighestRun

private theorem input_head_zero (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool)
    (i : Fin 27) (hi : keep i=false) : (ActiveTargetHighestRun.input G L ws a bs qs ns).head (Fin.castAdd 27 i)=0 := by
  unfold ActiveTargetHighestRun.input initial
  rw [FlatControlledShiftLayout.input_layout]
  fin_cases i
  all_goals first | rfl | simp [keep,right] at hi

private theorem input_tape_blank (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool)
    (i : Fin 27) (hi : keep i=false) : (ActiveTargetHighestRun.input G L ws a bs qs ns).tape (Fin.castAdd 27 i)=fun _ => blank := by
  unfold ActiveTargetHighestRun.input initial
  rw [FlatControlledShiftLayout.input_layout]
  fin_cases i
  all_goals first | rfl | simp [keep,right] at hi

private theorem input_descriptor_0 (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool)
    (a b : Array G L B) (bs qs ns : List Bool) :
    (ActiveTargetHighestRun.input G L ws a bs qs ns).head (2 : Fin 54)=
      (ActiveTargetHighestRun.input G L ws b bs qs ns).head (2 : Fin 54) ∧
    (ActiveTargetHighestRun.input G L ws a bs qs ns).tape (2 : Fin 54)=
      (ActiveTargetHighestRun.input G L ws b bs qs ns).tape (2 : Fin 54) := by
  unfold ActiveTargetHighestRun.input initial
  rw [FlatControlledShiftLayout.input_layout,FlatControlledShiftLayout.input_layout]
  rw [show (2 : Fin 54)=Fin.castAdd 27 (Fin.castAdd 17 (2 : Fin 10)) by rfl]
  simp only [PrefixCounterInit.tapeCount,Nat.reduceAdd,Tapes.append,Fin.addCases_left]
  exact ⟨trivial,trivial⟩

private theorem input_descriptor_1 (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool)
    (a b : Array G L B) (bs qs ns : List Bool) :
    (ActiveTargetHighestRun.input G L ws a bs qs ns).head (5 : Fin 54)=
      (ActiveTargetHighestRun.input G L ws b bs qs ns).head (5 : Fin 54) ∧
    (ActiveTargetHighestRun.input G L ws a bs qs ns).tape (5 : Fin 54)=
      (ActiveTargetHighestRun.input G L ws b bs qs ns).tape (5 : Fin 54) := by
  unfold ActiveTargetHighestRun.input initial
  rw [FlatControlledShiftLayout.input_layout,FlatControlledShiftLayout.input_layout]
  rw [show (5 : Fin 54)=Fin.castAdd 27 (Fin.castAdd 17 (5 : Fin 10)) by rfl]
  simp only [PrefixCounterInit.tapeCount,Nat.reduceAdd,Tapes.append,Fin.addCases_left]
  exact ⟨trivial,trivial⟩

private theorem input_descriptor_2 (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool)
    (a b : Array G L B) (bs qs ns : List Bool) :
    (ActiveTargetHighestRun.input G L ws a bs qs ns).head (8 : Fin 54)=
      (ActiveTargetHighestRun.input G L ws b bs qs ns).head (8 : Fin 54) ∧
    (ActiveTargetHighestRun.input G L ws a bs qs ns).tape (8 : Fin 54)=
      (ActiveTargetHighestRun.input G L ws b bs qs ns).tape (8 : Fin 54) := by
  unfold ActiveTargetHighestRun.input initial
  rw [FlatControlledShiftLayout.input_layout,FlatControlledShiftLayout.input_layout]
  rw [show (8 : Fin 54)=Fin.castAdd 27 (Fin.castAdd 17 (8 : Fin 10)) by rfl]
  simp only [PrefixCounterInit.tapeCount,Nat.reduceAdd,Tapes.append,Fin.addCases_left]
  exact ⟨trivial,trivial⟩

private theorem input_descriptor_3 (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool)
    (a b : Array G L B) (bs qs ns : List Bool) :
    (ActiveTargetHighestRun.input G L ws a bs qs ns).head (15 : Fin 54)=
      (ActiveTargetHighestRun.input G L ws b bs qs ns).head (15 : Fin 54) ∧
    (ActiveTargetHighestRun.input G L ws a bs qs ns).tape (15 : Fin 54)=
      (ActiveTargetHighestRun.input G L ws b bs qs ns).tape (15 : Fin 54) := by
  unfold ActiveTargetHighestRun.input initial
  rw [FlatControlledShiftLayout.input_layout,FlatControlledShiftLayout.input_layout]
  rw [show (15 : Fin 54)=Fin.castAdd 27 (Fin.natAdd 10 (5 : Fin 17)) by rfl]
  simp only [PrefixCounterInit.tapeCount,Nat.reduceAdd,Tapes.append,Fin.addCases_left,Fin.addCases_right,FlatControlledShiftLayout.suffix,
    FlatControlledShiftLayout.descriptorHead,FlatControlledShiftLayout.descriptorTape,
    Matrix.cons_val_zero]
  constructor
  · trivial
  · simp only [Matrix.cons_val]

private theorem input_descriptor_4 (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool)
    (a b : Array G L B) (bs qs ns : List Bool) :
    (ActiveTargetHighestRun.input G L ws a bs qs ns).head (17 : Fin 54)=
      (ActiveTargetHighestRun.input G L ws b bs qs ns).head (17 : Fin 54) ∧
    (ActiveTargetHighestRun.input G L ws a bs qs ns).tape (17 : Fin 54)=
      (ActiveTargetHighestRun.input G L ws b bs qs ns).tape (17 : Fin 54) := by
  unfold ActiveTargetHighestRun.input initial
  rw [FlatControlledShiftLayout.input_layout,FlatControlledShiftLayout.input_layout]
  rw [show (17 : Fin 54)=Fin.castAdd 27 (Fin.natAdd 10 (7 : Fin 17)) by rfl]
  simp only [PrefixCounterInit.tapeCount,Nat.reduceAdd,Tapes.append,Fin.addCases_left,Fin.addCases_right,FlatControlledShiftLayout.suffix,
    FlatControlledShiftLayout.descriptorHead,FlatControlledShiftLayout.descriptorTape,
    Matrix.cons_val_zero]
  constructor
  · trivial
  · simp only [Matrix.cons_val]

private theorem input_descriptor_5 (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool)
    (a b : Array G L B) (bs qs ns : List Bool) :
    (ActiveTargetHighestRun.input G L ws a bs qs ns).head (26 : Fin 54)=
      (ActiveTargetHighestRun.input G L ws b bs qs ns).head (26 : Fin 54) ∧
    (ActiveTargetHighestRun.input G L ws a bs qs ns).tape (26 : Fin 54)=
      (ActiveTargetHighestRun.input G L ws b bs qs ns).tape (26 : Fin 54) := by
  unfold ActiveTargetHighestRun.input initial
  rw [FlatControlledShiftLayout.input_layout,FlatControlledShiftLayout.input_layout]
  rw [show (26 : Fin 54)=Fin.castAdd 27 (Fin.natAdd 10 (16 : Fin 17)) by rfl]
  simp only [PrefixCounterInit.tapeCount,Nat.reduceAdd,Tapes.append,Fin.addCases_left,Fin.addCases_right,FlatControlledShiftLayout.suffix,
    FlatControlledShiftLayout.descriptorHead,FlatControlledShiftLayout.descriptorTape,
    Matrix.cons_val_zero]
  constructor
  · trivial
  · simp only [Matrix.cons_val]

private theorem input_source (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool)
    (a : Array G L B) (bs qs ns : List Bool) :
    (ActiveTargetHighestRun.input G L ws a bs qs ns).head (20 : Fin 54)=0 ∧
    (ActiveTargetHighestRun.input G L ws a bs qs ns).tape (20 : Fin 54)=
      fun z => RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 (List.ofFn a) z) := by
  unfold ActiveTargetHighestRun.input initial
  rw [FlatControlledShiftLayout.input_layout]
  exact ⟨rfl,rfl⟩

/-- Every original descriptor is retained and every private cell is blank,
so the exact clean output is the same ActiveTargetHighestRun.input bank with its array changed. -/
theorem output_eq_input (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool) :
    output G L ws a bs qs ns=ActiveTargetHighestRun.input G L ws (array G L a) bs qs ns := by
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases with
    | left i =>
      by_cases hs : i.val=20
      · have he : Fin.castAdd 27 i=(20 : Fin 54) := Fin.ext hs
        rw [he]
        exact (output_origin G L ws a bs qs ns).trans (input_source G L ws (array G L a) bs qs ns).1.symm
      · by_cases hk : keep i=false
        · exact (private_blank G L ws a bs qs ns i hk).1.trans
            (input_head_zero G L ws (array G L a) bs qs ns i hk).symm
        · fin_cases i
          all_goals solve
            | simp [keep,right] at hk
            | exact (hs rfl).elim
            | exact (descriptors_retained G L ws a bs qs ns 0).1.trans (input_descriptor_0 G L ws a (array G L a) bs qs ns).1
    | right i =>
      simp only [Fin.addCases_right,SharedBank.empty]
  · funext i
    induction i using Fin.addCases with
    | left i =>
      by_cases hs : i.val=20
      · have he : Fin.castAdd 27 i=(20 : Fin 54) := Fin.ext hs
        rw [he]
        exact (output_array G L ws a bs qs ns).trans (input_source G L ws (array G L a) bs qs ns).2.symm
      · by_cases hk : keep i=false
        · exact (private_blank G L ws a bs qs ns i hk).2.trans
            (input_tape_blank G L ws (array G L a) bs qs ns i hk).symm
        · fin_cases i
          all_goals solve
            | simp [keep,right] at hk
            | exact (hs rfl).elim
            | exact (descriptors_retained G L ws a bs qs ns 0).2.trans (input_descriptor_0 G L ws a (array G L a) bs qs ns).2
            | exact (descriptors_retained G L ws a bs qs ns 1).2.trans (input_descriptor_1 G L ws a (array G L a) bs qs ns).2
            | exact (descriptors_retained G L ws a bs qs ns 2).2.trans (input_descriptor_2 G L ws a (array G L a) bs qs ns).2
            | exact (descriptors_retained G L ws a bs qs ns 3).2.trans (input_descriptor_3 G L ws a (array G L a) bs qs ns).2
            | exact (descriptors_retained G L ws a bs qs ns 4).2.trans (input_descriptor_4 G L ws a (array G L a) bs qs ns).2
            | exact (descriptors_retained G L ws a bs qs ns 5).2.trans (input_descriptor_5 G L ws a (array G L a) bs qs ns).2
    | right i =>
      simp only [Fin.addCases_right,SharedBank.empty]

end
end IntegerMultBounds.Machine.ActiveTargetHighestLaterClean
