import IntegerMultBounds.Machine.CompactAllAxisPhaseControls
import IntegerMultBounds.Machine.RepeatedWeightedPhaseTensor
import IntegerMultBounds.Machine.UnitPhaseSigned

/-! The one-traversal all-axis accumulator computes the complete tensor phase
of an actual complex25 edge, rather than the phase of a single axis. -/
namespace IntegerMultBounds.Machine.CompactAllAxisPhaseReadout
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageRuntimeOrdinal (reverseAxis)
open Networks Networks.ComplexPhaseRowSchedule
variable {s : Shape}

def delta (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) : ZMod 4 :=
  BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
    (target edge) (target_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates input hslots k axis))-
  BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
    (source edge) (source_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates input hslots k axis))

def reversal (f : ℕ) : Fin f ≃ Fin f where
  toFun := reverseAxis
  invFun := reverseAxis
  left_inv := by intro i; apply Fin.ext; simp only [reverseAxis]; have := i.isLt; omega
  right_inv := by intro i; apply Fin.ext; simp only [reverseAxis]; have := i.isLt; omega

theorem axis_readout (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) :
    WeightedPhaseAccumulator.weightedSum (CompactComplexPhaseControlCodec.weights edge).reverse
      (CompactComplexPhaseControlCodec.bits input hslots edge k axis).reverse=
      delta input hslots edge k axis := by
  have hl := CompactComplexPhaseControlCodec.lengths input hslots edge k axis
  rw [CompactComplexPhaseSparseControls.weighted_reverse _ _ hl.symm]
  have hr := CompactComplexPhaseControlCodec.readout input hslots edge k axis
  rw [WeightedPhaseAccumulator.accumulate_cast _ _ _ hl] at hr
  simpa only [delta,Fin.val_zero,Nat.cast_zero,zero_add] using hr

def bits (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (hm : 0<dimension edge) :=
  SelectedSourceBitsData.selected (CompactComplexPhaseRecordAddress.address input hslots edge k)
    s.chunk (CompactAllAxisPhaseControls.start input hslots edge hm) (dimension edge*input.stage.f)

theorem matrix_entry (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (hm : 0<dimension edge)
    (i : Fin (CompactComplexPhaseControlCodec.weights edge).reverse.length) (j : Fin input.stage.f) :
    (bits input hslots edge k hm).getD (i.val*input.stage.f+j.val) false=
      (CompactComplexPhaseControlCodec.bits input hslots edge k (reverseAxis j)).reverse.getD i.val false := by
  have hi : i.val<dimension edge := by
    simpa only [List.length_reverse,CompactComplexPhaseControlCodec.weights,List.length_ofFn] using i.isLt
  have hj := j.isLt
  have hflat : i.val*input.stage.f+j.val<(bits input hslots edge k hm).length := by
    simp only [bits,SelectedSourceBitsData.selected_length]
    nlinarith
  have hcol : i.val<(CompactComplexPhaseControlCodec.bits input hslots edge k (reverseAxis j)).reverse.length := by
    simpa only [List.length_reverse,CompactComplexPhaseControlCodec.bits,List.length_ofFn] using hi
  rw [List.getD_eq_getElem _ _ hflat,List.getD_eq_getElem _ _ hcol,List.getElem_reverse]
  have he := CompactAllAxisPhaseControls.extracted_entry input hslots edge k hm ⟨i.val,hi⟩ j
  have hidx : dimension edge-i.val-1=dimension edge-1-i.val := by omega
  simpa only [bits,CompactComplexPhaseControlCodec.bits,List.length_ofFn,hidx] using he

theorem total_readout (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (hm : 0<dimension edge) :
    RepeatedWeightedPhaseAccumulator.total (CompactComplexPhaseControlCodec.weights edge).reverse
      (fun i => (bits input hslots edge k hm).getD i false) input.stage.f=
      ∑ axis : Fin input.stage.f,delta input hslots edge k axis := by
  rw [RepeatedWeightedPhaseTensor.matrix_total _ _ _
    (fun j => (CompactComplexPhaseControlCodec.bits input hslots edge k (reverseAxis j)).reverse)
    (by intro j; simp [CompactComplexPhaseControlCodec.bits,CompactComplexPhaseControlCodec.weights])
    (matrix_entry input hslots edge k hm)]
  simp_rw [axis_readout]
  exact (reversal input.stage.f).sum_comp (delta input hslots edge k)

theorem accumulator_readout (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (hm : 0<dimension edge) :
    ((RepeatedWeightedPhaseAccumulator.accumulate 0 (CompactComplexPhaseControlCodec.weights edge).reverse
      (fun i => (bits input hslots edge k hm).getD i false) input.stage.f).val : ZMod 4)=
      ∑ axis : Fin input.stage.f,delta input hslots edge k axis := by
  rw [RepeatedWeightedPhaseAccumulator.accumulate_cast,total_readout]
  simp

/-- One arithmetic application realizes the complete product of axis phases. -/
theorem coefficient_phase (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (hm : 0<dimension edge)
    (xs : ℕ → List (Fin 2)) (b n : ℕ) (hw : ∀ j,(xs j).length=b+1)
    (hg : ∀ j : Fin 2,|ButterflySigned.signedValue b (xs j.val)|<(2^b : ℕ)) :
    let p := RepeatedWeightedPhaseAccumulator.accumulate 0
      (CompactComplexPhaseControlCodec.weights edge).reverse
      (fun i => (bits input hslots edge k hm).getD i false) input.stage.f
    ButterflySigned.complexValue
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words p 0 xs))
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words p 1 xs)) n=
      (∏ axis : Fin input.stage.f,BinaryPhase.phase (delta input hslots edge k axis))*
        ButterflySigned.complexValue (ButterflySigned.signedValue b (xs 0))
          (ButterflySigned.signedValue b (xs 1)) n := by
  have hr := UnitPhaseSigned.words_phase
    (RepeatedWeightedPhaseAccumulator.accumulate 0 (CompactComplexPhaseControlCodec.weights edge).reverse
      (fun i => (bits input hslots edge k hm).getD i false) input.stage.f) xs b n hw hg
  rw [accumulator_readout,BinaryPhase.phase_sum] at hr
  exact hr

end
end IntegerMultBounds.Machine.CompactAllAxisPhaseReadout
