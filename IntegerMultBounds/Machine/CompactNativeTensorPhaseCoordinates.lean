import IntegerMultBounds.Machine.CompactNativePhaseCoordinates
import IntegerMultBounds.Machine.CompactAllAxisPhaseReadout

/-! The single all-axis scanner reads the row actually reached by the native
basis word. Its one coefficient rotation is therefore the complete original
complex-edge tensor phase, including every coordinate axis and spectator. -/
namespace IntegerMultBounds.Machine.CompactNativeTensorPhaseCoordinates
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageTripleWords (count)
open ActivePrefixStageNativePairCoordinates (start)
open Networks Networks.ComplexPhaseRowSchedule
variable {s : Shape}

def controls (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge)
    (hm : 0<dimension edge) (r : Fin (count d)) :=
  SelectedSourceBitsData.selected (BinaryAddressTableData.row s.bits r.val) s.chunk
    (CompactAllAxisPhaseControls.start d hslots edge hm) (dimension edge*d.stage.f)

def phase (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge)
    (hm : 0<dimension edge) (r : Fin (count d)) :=
  RepeatedWeightedPhaseAccumulator.accumulate 0 (CompactComplexPhaseControlCodec.weights edge).reverse
    (fun i => (controls d hslots edge hm r).getD i false) d.stage.f

/-- Actual native row ordinals determine the complete phase of the original
input row, without an address-serialization compatibility assumption. -/
theorem phase_after_word (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge)
    (hm : 0<dimension edge) (r : Fin (count d)) :
    ((phase d hslots edge hm (ActivePrefixStageNativePairCoordinates.run d (CompactComplexPhasePhysical.word d hslots edge) r)).val : ZMod 4)=
      ∑ axis : Fin d.stage.f,CompactAllAxisPhaseReadout.delta d hslots edge (start d r) axis := by
  have h := CompactAllAxisPhaseReadout.accumulator_readout d hslots edge (start d r) hm
  unfold CompactAllAxisPhaseReadout.bits at h
  rw [CompactNativePhaseCoordinates.address_after_word] at h
  exact h

/-- One signed rotation at the physically reached row gives the product of
all original coordinate phases; no per-axis coefficient pass is required. -/
theorem coefficient_phase (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge)
    (hm : 0<dimension edge) (r : Fin (count d)) (xs : ℕ → List (Fin 2)) (b n : ℕ)
    (hw : ∀ j,(xs j).length=b+1)
    (hg : ∀ j : Fin 2,|ButterflySigned.signedValue b (xs j.val)|<(2^b : ℕ)) :
    let p := phase d hslots edge hm (ActivePrefixStageNativePairCoordinates.run d (CompactComplexPhasePhysical.word d hslots edge) r)
    ButterflySigned.complexValue
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words p 0 xs))
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words p 1 xs)) n=
      (∏ axis : Fin d.stage.f,BinaryPhase.phase
        (CompactAllAxisPhaseReadout.delta d hslots edge (start d r) axis))*
        ButterflySigned.complexValue (ButterflySigned.signedValue b (xs 0))
          (ButterflySigned.signedValue b (xs 1)) n := by
  have h := UnitPhaseSigned.words_phase
    (phase d hslots edge hm (ActivePrefixStageNativePairCoordinates.run d (CompactComplexPhasePhysical.word d hslots edge) r)) xs b n hw hg
  rw [phase_after_word,BinaryPhase.phase_sum] at h
  exact h

end
end IntegerMultBounds.Machine.CompactNativeTensorPhaseCoordinates
