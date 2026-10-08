import IntegerMultBounds.Machine.FlatCoordinateShiftInput
import IntegerMultBounds.Machine.SharedBank

/-! Four common tapes for fully initialized shifts: payload, output scratch,
and the sole preserved exponent/record-width descriptors. All private input
tapes are literally blank, enabling schedules without copied input headers. -/
namespace IntegerMultBounds.Machine.FlatCoordinateShiftSharedBank
open Networks.Shared50ModularControl (prime)
open FlatCoordinateShiftFromDimensions
open FlatCoordinateShiftInput (exponentSlot widthSlot)
open FlatCoordinateSchedule (bits)
noncomputable section
variable {d b W : ℕ}

def slots (t : Fin d) : Fin 4 → Fin (TapeCount t) :=
  ![sourceSlot t,destSlot t,exponentSlot t,widthSlot t]

theorem slots_injective (t : Fin d) : Function.Injective (slots t) := by
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals simp [slots,FlatCoordinateShiftInput.sourceSlot_eq,FlatCoordinateShiftInput.destSlot_eq,
    exponentSlot,widthSlot] at hv

def headers (b W : ℕ) : Tapes 2 prime :=
  ⟨fun _ => 1,![RadixZeroFill.encodedBinary (bits b),RadixZeroFill.encodedBinary (bits W)]⟩

def common (a : FlatCoordinateStages.Array d b W) : Tapes 4 prime :=
  (FlatAffineScalingPayload.pair a).append (headers b W)

private theorem four (t : Fin d) (v : Tapes (TapeCount t) prime) :
    SharedBank.payload v (slots t) =
      (SharedPayload.payload v (sourceSlot t) (destSlot t)).append
        ⟨![v.head (exponentSlot t),v.head (widthSlot t)],
          ![v.tape (exponentSlot t),v.tape (widthSlot t)]⟩ := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem input_common (t : Fin d) (a : FlatCoordinateStages.Array d b W) :
    SharedBank.payload (FlatCoordinateShiftFromDimensions.input t b W a) (slots t) = common a := by
  rw [four,FlatCoordinateShiftInput.input_payload]
  congr 1
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [FlatCoordinateShiftFromDimensions.input,Tapes.append,exponentSlot,widthSlot,
      FlatCoordinateDimensions.input,TranslationDimensions.input,TranslationDimensions.bank]

theorem input_blank (t : Fin d) (a : FlatCoordinateStages.Array d b W) :
    SharedBank.strip (FlatCoordinateShiftFromDimensions.input t b W a) (slots t) =
      SharedBank.empty (TapeCount t) prime := by
  unfold SharedBank.strip SharedBank.empty
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    by_cases hi : ∃ j, slots t j = i
    · simp [hi]
    · have hb : i ≠ exponentSlot t := by intro h; exact hi ⟨2,h.symm⟩
      have hw : i ≠ widthSlot t := by intro h; exact hi ⟨3,h.symm⟩
      have hs : i ≠ sourceSlot t := by intro h; exact hi ⟨0,h.symm⟩
      have hh := FlatCoordinateShiftInput.workspace_blank t a i hb hw hs
      simp only [hi,ite_false]
      first | exact hh.1 | exact hh.2

theorem output_common (r : ℚ) (hr : Networks.Shared50AffineCoefficients.Occurs r)
    (t k : Fin d) (hk : k < t) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W) :
    SharedBank.payload (output r hr t k hk b W hW a) (slots t) =
      common (FlatCoordinateShift.array (radix := prime) r a t k hk) := by
  rw [four,output_payload]
  apply congrArg (Tapes.append _)
  have hd := output_dimensions r hr t k hk b W hW a
  have hh := congrArg (fun v : Tapes 9 prime =>
    (⟨![v.head 2,v.head 3],![v.tape 2,v.tape 3]⟩ : Tapes 2 prime)) hd
  have he : (⟨![(FlatCoordinateDimensions.output t b W).head 2,(FlatCoordinateDimensions.output t b W).head 3],
      ![(FlatCoordinateDimensions.output t b W).tape 2,(FlatCoordinateDimensions.output t b W).tape 3]⟩ : Tapes 2 prime) = headers b W := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at hh
  simpa only [Placement.extra,stagePlacement,Equiv.coe_fn_mk,Fin.addCases_right,exponentSlot,widthSlot] using hh

end
end IntegerMultBounds.Machine.FlatCoordinateShiftSharedBank
