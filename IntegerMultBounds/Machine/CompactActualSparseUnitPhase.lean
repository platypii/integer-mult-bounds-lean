import IntegerMultBounds.Machine.CompactComplexPhaseSparseControls
import IntegerMultBounds.Machine.SparseWeightedUnitPhase

/-! Actual literal phase application from a complete runtime destination
address and two signed numerator records. Physical extraction, accumulation,
flag readout and arithmetic are one composed machine, with payload charging. -/
namespace IntegerMultBounds.Machine.CompactActualSparseUnitPhase
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open CompactComplexPhaseSparseControls (address stride start)
open Networks Networks.ComplexPhaseRowSchedule
variable {s : Shape}

def program (edge : Edge) := SparseWeightedUnitPhase.program (CompactComplexPhaseControlCodec.weights edge).reverse

theorem runs (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) (hdim : 0<dimension edge)
    (hs : Fin 3 → List Bool) (xs : ℕ → List (Fin 2)) (w : ℕ) (hw : ∀ j,(xs j).length=w)
    (hq : Counter.value (hs 0)=stride input)
    (hn : Counter.value (hs 1)=dimension edge-1)
    (hr : Counter.value (hs 2)=start input hslots edge axis hdim)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    HoareTime (program edge)
      (fun v => v=SparseWeightedUnitPhase.input (address input hslots edge k) hs xs)
      (fun v => v=SparseWeightedUnitPhase.output (CompactComplexPhaseControlCodec.weights edge).reverse
        (address input hslots edge k) hs (stride input) (start input hslots edge axis hdim) (dimension edge-1) xs)
      (400*s.payload+2*dimension edge+12*w+47) := by
  have hl : dimension edge-1+1=(CompactComplexPhaseControlCodec.weights edge).reverse.length := by
    simp only [List.length_reverse,CompactComplexPhaseControlCodec.weights,List.length_ofFn]
    omega
  have hspan : start input hslots edge axis hdim+(dimension edge-1)*stride input<
      (address input hslots edge k).length := by
    simpa only [address,BinaryAddressTableData.row_length] using
      CompactComplexPhaseSparseControls.span input hslots edge axis hdim
  have hpos : 1≤stride input := Nat.mul_pos input.stage.positiveWidth
    (by have := input.stage.selectedFits; omega)
  have h := SparseWeightedUnitPhase.runs (CompactComplexPhaseControlCodec.weights edge).reverse
    (address input hslots edge k) hs (stride input) (start input hslots edge axis hdim) (dimension edge-1)
    hl xs w hw hspan hpos hq hn hr hc
  apply h.consequence (fun _ h => h) (fun _ h => h) _
  have hcharge := CompactComplexPhaseSparseControls.extraction_charge input
  simpa only [address,BinaryAddressTableData.row_length,List.length_reverse,
    CompactComplexPhaseControlCodec.weights,List.length_ofFn,Nat.add_assoc] using
      Nat.add_le_add_right hcharge (2*dimension edge+12*w+47)

theorem phase_correct (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) (hdim : 0<dimension edge)
    (xs : ℕ → List (Fin 2)) (b n : ℕ) (hw : ∀ j,(xs j).length=b+1)
    (hguard : ∀ j : Fin 2,|ButterflySigned.signedValue b (xs j.val)|<(2^b : ℕ)) :
    let p := WeightedPhaseAccumulator.accumulate 0 (CompactComplexPhaseControlCodec.weights edge).reverse
      (SparseWeightedUnitPhase.selected (address input hslots edge k) (stride input)
        (start input hslots edge axis hdim) (dimension edge-1))
    ButterflySigned.complexValue (ButterflySigned.signedValue b (UnitPhaseNumerator.words p 0 xs))
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words p 1 xs)) n=
      BinaryPhase.phase
        (BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
          (target edge) (target_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates input hslots k axis))-
        BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
          (source edge) (source_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates input hslots k axis)))*
      ButterflySigned.complexValue (ButterflySigned.signedValue b (xs 0)) (ButterflySigned.signedValue b (xs 1)) n := by
  dsimp only
  rw [UnitPhaseSigned.words_phase _ xs b n hw hguard]
  have hn' : dimension edge-1+1=dimension edge := by omega
  simp only [SparseWeightedUnitPhase.selected,hn']
  rw [CompactComplexPhaseSparseControls.extracted_readout]

end
end IntegerMultBounds.Machine.CompactActualSparseUnitPhase
