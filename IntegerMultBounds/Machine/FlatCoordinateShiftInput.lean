import IntegerMultBounds.Machine.FlatCoordinateShiftFromDimensions

/-! Initial payload and private-bank contracts for the fully synthesized shift.
Only b/W and the original array are supplied; all private metadata is independent
of that array and no intermediate payload is encoded in the input. -/
namespace IntegerMultBounds.Machine.FlatCoordinateShiftInput
open FlatCoordinateShiftFromDimensions
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
variable {d b W : ℕ}

@[simp] theorem sourceSlot_eq (t : Fin d) :
    sourceSlot t = Fin.natAdd (9+prefixTapes t) (10 : Fin 17) := by
  simp [sourceSlot,stagePlacement,FlatControlledShiftPayload.sourceSlot]

@[simp] theorem destSlot_eq (t : Fin d) :
    destSlot t = Fin.natAdd (9+prefixTapes t) (11 : Fin 17) := by
  simp [destSlot,stagePlacement,FlatControlledShiftPayload.destSlot]

theorem slots_distinct (t : Fin d) : sourceSlot t ≠ destSlot t := by
  intro h
  have hh := congrArg Fin.val h
  simp only [sourceSlot_eq,destSlot_eq,Fin.val_natAdd] at hh
  omega

theorem input_payload (t : Fin d) (a : FlatCoordinateStages.Array d b W) :
    SharedPayload.payload (FlatCoordinateShiftFromDimensions.input t b W a) (sourceSlot t) (destSlot t) =
      FlatAffineScalingPayload.pair a := by
  simp only [SharedPayload.payload,sourceSlot_eq,destSlot_eq]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [FlatCoordinateShiftFromDimensions.input,Tapes.append,FlatControlledShiftLayout.suffix,RadixToBinary.binaryEncoding,blank]

private theorem setTape_right {l r q : ℕ} (v : Tapes l q) (w : Tapes r q) (i : Fin r)
    (f : ℤ → Fin (q+4)) (p : ℤ) :
    setTape (v.append w) (Fin.natAdd l i) f p = v.append (setTape w i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals rename_i k; intro h; have hk := k.isLt; omega

private theorem clear_suffix (f g : ℤ → Fin 4) :
    setTape (FlatControlledShiftLayout.suffix prime f (fun _ => blank) 0 0 none none none)
      10 (fun _ => blank) 0 =
    setTape (FlatControlledShiftLayout.suffix prime g (fun _ => blank) 0 0 none none none)
      10 (fun _ => blank) 0 := by
  unfold setTape FlatControlledShiftLayout.suffix
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i; fin_cases i <;> simp

theorem strip_input_eq (t : Fin d) (a a' : FlatCoordinateStages.Array d b W) :
    SharedPayload.strip (FlatCoordinateShiftFromDimensions.input t b W a) (sourceSlot t) (destSlot t) =
      SharedPayload.strip (FlatCoordinateShiftFromDimensions.input t b W a') (sourceSlot t) (destSlot t) := by
  unfold SharedPayload.strip
  rw [sourceSlot_eq,destSlot_eq]
  unfold FlatCoordinateShiftFromDimensions.input
  rw [setTape_right,setTape_right,setTape_right,setTape_right,clear_suffix]

def exponentSlot (t : Fin d) : Fin (TapeCount t) := Fin.castAdd 17 (Fin.castAdd (prefixTapes t) (2 : Fin 9))
def widthSlot (t : Fin d) : Fin (TapeCount t) := Fin.castAdd 17 (Fin.castAdd (prefixTapes t) (3 : Fin 9))

theorem workspace_blank (t : Fin d) (a : FlatCoordinateStages.Array d b W) (i : Fin (TapeCount t))
    (hb : i ≠ exponentSlot t) (hw : i ≠ widthSlot t) (hs : i ≠ sourceSlot t) :
    (FlatCoordinateShiftFromDimensions.input t b W a).head i = 0 ∧
    (FlatCoordinateShiftFromDimensions.input t b W a).tape i = fun _ => blank := by
  rw [sourceSlot_eq] at hs
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      have hb' : i ≠ TranslationDimensions.exponentSlot := by
        intro h; subst i; exact hb rfl
      have hw' : i ≠ TranslationDimensions.widthSlot := by
        intro h; subst i; exact hw rfl
      simpa only [FlatCoordinateShiftFromDimensions.input,Tapes.append,Fin.addCases_left] using
        FlatCoordinateDimensions.input_workspace_blank b W i hb' hw'
    | right i =>
      simp [FlatCoordinateShiftFromDimensions.input,Tapes.append,PrefixWidthCopies.blankBank]
  | right i =>
    have hi : i ≠ 10 := by intro h; subst i; exact hs rfl
    fin_cases i <;> simp_all [FlatCoordinateShiftFromDimensions.input,Tapes.append,
      FlatControlledShiftLayout.suffix,FlatControlledShiftLayout.descriptorHead,
      FlatControlledShiftLayout.descriptorTape,RadixToBinary.binaryEncoding,blank]

end IntegerMultBounds.Machine.FlatCoordinateShiftInput
