import IntegerMultBounds.Machine.FlatCoordinateScalingConstruct
import IntegerMultBounds.Machine.FlatCoordinateShiftSharedBank

/-! A fully initialized scaling shares only payload/scratch and b/W. -/
namespace IntegerMultBounds.Machine.FlatCoordinateScalingSharedBank
open FlatAffineScalingInputLayout (Kind kinds coefficientKinds)
open Networks.Shared50ModularControl (prime)
open FlatCoordinateShiftSharedBank (common headers)
noncomputable section
variable {d b W : ℕ}

private def NoPayload {n : ℕ} (ks : Fin n → Kind) : Prop := ∀ i, ks i ≠ .payload
private def Single {n : ℕ} (ks : Fin n → Kind) (j : Fin n) : Prop := ∀ i, ks i = .payload ↔ i = j

private theorem NoPayload.append {m n : ℕ} {ks : Fin m → Kind} {ls : Fin n → Kind}
    (h : NoPayload ks) (h' : NoPayload ls) : NoPayload (Fin.addCases ks ls) := by
  intro i
  induction i using Fin.addCases with
  | left i => simpa using h i
  | right i => simpa using h' i

private theorem Single.left {m n : ℕ} {ks : Fin m → Kind} {ls : Fin n → Kind} {j : Fin m}
    (h : Single ks j) (h' : NoPayload ls) : Single (Fin.addCases ks ls) (Fin.castAdd n j) := by
  intro i
  induction i using Fin.addCases with
  | left i => simpa using h i
  | right i =>
    simp only [Fin.addCases_right, h' i, false_iff]
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    have := j.isLt
    omega

private theorem Single.right {m n : ℕ} {ks : Fin m → Kind} {ls : Fin n → Kind} {j : Fin n}
    (h : NoPayload ks) (h' : Single ls j) : Single (Fin.addCases ks ls) (Fin.natAdd m j) := by
  intro i
  induction i using Fin.addCases with
  | left i =>
    simp only [Fin.addCases_left, h i, false_iff]
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    have := i.isLt
    omega
  | right i => simpa using h' i

private theorem coefficient_none (c : ℕ) : NoPayload (coefficientKinds c .work) := by
  unfold coefficientKinds
  repeat' apply NoPayload.append
  all_goals intro i
  all_goals first | exact Kind.noConfusion | (fin_cases i <;> decide)

private theorem coefficient_single (c : ℕ) :
    Single (coefficientKinds c .payload)
      (Fin.natAdd (ScalingPreparedExecution.SynthesisTapes c) (Fin.castAdd 2 (Fin.castAdd c (0 : Fin 4)))) := by
  unfold coefficientKinds
  apply Single.right
  · repeat' apply NoPayload.append
    all_goals intro i
    all_goals first | exact Kind.noConfusion | (fin_cases i <;> decide)
  · apply Single.left
    · apply Single.left
      · intro i; fin_cases i <;> decide
      · intro i; exact Kind.noConfusion
    · intro i; fin_cases i <;> decide

/-- The classifier labels exactly the physical scaler source as payload. -/
theorem kinds_payload (r : ℚ) (i : Fin (FlatAffineScalingInstall.LocalTapes r.num.natAbs r.den)) :
    kinds r.num.natAbs r.den i = .payload ↔ i = FlatAffineScaling.sourceSlot r := by
  have h : Single (kinds r.num.natAbs r.den) (FlatAffineScaling.sourceSlot r) := by
    unfold kinds FlatAffineScaling.sourceSlot
    apply Single.left
    · apply Single.left
      · apply Single.left
        · apply Single.left
          · exact (coefficient_single _).left (coefficient_none _)
          · intro j; fin_cases j <;> decide
        · apply NoPayload.append
          · intro j; fin_cases j <;> decide
          · intro j; fin_cases j <;> decide
      · intro j; fin_cases j <;> decide
    · intro j; fin_cases j <;> decide
  exact h i

abbrev TapeCount (r : ℚ) := FlatAffineScalingInstall.TapeCount r.num.natAbs r.den

def sourceSlot (r : ℚ) : Fin (TapeCount r) := Fin.natAdd 9 (FlatAffineScaling.sourceSlot r)
def destSlot (r : ℚ) : Fin (TapeCount r) := Fin.natAdd 9 (ActualAffineScalingStream.destinationSlot r)
def exponentSlot (r : ℚ) : Fin (TapeCount r) := Fin.castAdd _ (2 : Fin 9)
def widthSlot (r : ℚ) : Fin (TapeCount r) := Fin.castAdd _ (3 : Fin 9)
def slots (r : ℚ) : Fin 4 → Fin (TapeCount r) := ![sourceSlot r,destSlot r,exponentSlot r,widthSlot r]

theorem slots_injective (r : ℚ) : Function.Injective (slots r) := by
  have hd : sourceSlot r ≠ destSlot r := by
    intro h
    apply FlatAffineScalingPayload.slots_distinct r
    apply Fin.ext
    have hv := congrArg Fin.val h
    change 9+(FlatAffineScaling.sourceSlot r).val = 9+(ActualAffineScalingStream.destinationSlot r).val at hv
    omega
  have hs : 9 ≤ (sourceSlot r).val := by simp [sourceSlot]
  have ht : 9 ≤ (destSlot r).val := by simp [destSlot]
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals first
    | exact (hd h).elim
    | exact (hd h.symm).elim
    | (simp [slots,exponentSlot,widthSlot] at hv <;> omega)

private theorem four (r : ℚ) (v : Tapes (TapeCount r) prime) :
    SharedBank.payload v (slots r) =
      (SharedPayload.payload v (sourceSlot r) (destSlot r)).append
        ⟨![v.head (exponentSlot r),v.head (widthSlot r)],
          ![v.tape (exponentSlot r),v.tape (widthSlot r)]⟩ := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem input_common {r : ℚ} (hr : Networks.Shared50AffineCoefficients.ScaleOccurs r)
    (t : Fin d) (a : FlatCoordinateStages.Array d b W) :
    SharedBank.payload (FlatCoordinateScalingConstruct.input (r := r) a t) (slots r) = common a := by
  rw [four,sourceSlot,destSlot,FlatCoordinateScalingConstruct.input_payload hr]
  congr 1
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [FlatCoordinateScalingConstruct.input,Tapes.append,exponentSlot,widthSlot,
      FlatCoordinateDimensions.input,TranslationDimensions.input,TranslationDimensions.bank]

theorem output_common {r : ℚ} (hr : Networks.Shared50AffineCoefficients.ScaleOccurs r)
    (t : Fin d) (a : FlatCoordinateStages.Array d b W) :
    SharedBank.payload (FlatCoordinateScalingConstruct.output hr a t) (slots r) =
      common (FlatCoordinateScaling.array hr a t) := by
  rw [four,sourceSlot,destSlot,FlatCoordinateScalingConstruct.output_payload]
  congr 1
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [FlatCoordinateScalingConstruct.output,Tapes.append,exponentSlot,widthSlot,
      FlatCoordinateDimensions.output,TranslationDimensions.output,TranslationDimensions.bank]

theorem input_blank {r : ℚ} (t : Fin d) (a : FlatCoordinateStages.Array d b W) :
    SharedBank.strip (FlatCoordinateScalingConstruct.input (r := r) a t) (slots r) =
      SharedBank.empty (TapeCount r) prime := by
  have hh (i : Fin (TapeCount r)) (hi : ¬ ∃ j, slots r j = i) :
      (FlatCoordinateScalingConstruct.input (r := r) a t).head i = 0 ∧
      (FlatCoordinateScalingConstruct.input (r := r) a t).tape i = fun _ => blank := by
    induction i using Fin.addCases with
    | left i =>
      have hb : i ≠ TranslationDimensions.exponentSlot := by
        intro he; subst i; exact hi ⟨2,rfl⟩
      have hw : i ≠ TranslationDimensions.widthSlot := by
        intro he; subst i; exact hi ⟨3,rfl⟩
      simpa only [FlatCoordinateScalingConstruct.input,Tapes.append,Fin.addCases_left] using
        FlatCoordinateDimensions.input_workspace_blank b W i hb hw
    | right i =>
      apply FlatCoordinateScalingConstruct.input_workspace_blank a t i
      intro he
      have hs := (kinds_payload r i).mp he
      exact hi ⟨0,by simp [slots,sourceSlot,hs]⟩
  unfold SharedBank.strip SharedBank.empty
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    by_cases hi : ∃ j, slots r j = i
    · simp [hi]
    · simp only [hi,ite_false]
      first | exact (hh i hi).1 | exact (hh i hi).2

end
end IntegerMultBounds.Machine.FlatCoordinateScalingSharedBank
