import IntegerMultBounds.Machine.CompactComplexPhasePhysical
import IntegerMultBounds.Machine.WeightedUnitPhase

/-! Actual residual weights and physically computed address controls determine
a literal Boolean control word. Its machine computes the modulo-four phase
and applies that phase to centered signed Gaussian dyadic numerator records. -/
namespace IntegerMultBounds.Machine.CompactComplexPhaseControlCodec
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open Networks Networks.ComplexPhaseRowSchedule
open CompactComplexPhasePhysical (control diagonal originalCoordinates)
variable {s : Shape}

def weight (edge : Edge) (i : Fin (dimension edge)) : ZMod 4 :=
  BinaryPhase.weightPhase (BinaryPhaseResidualRowProgram.basis ComplexPhaseBudget.coordinateSymm
    (low edge) (high edge) (low_nondegenerate edge) (high_nondegenerate edge)
    (comparable edge) (residual_good edge) i : Fin (25^3) → ZMod 2)

def weights (edge : Edge) : List (ZMod 4) :=
  List.ofFn (fun i => if direction edge then -weight edge i else weight edge i)

def bits (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) : List Bool :=
  List.ofFn (fun i => BinaryRowColumns.bit (control input hslots edge k axis i))

theorem lengths (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) :
    (bits input hslots edge k axis).length=(weights edge).length := by simp [bits,weights]

private theorem zip_ofFn {α β γ : Type*} {n : ℕ} (f : α → β → γ) (x : Fin n → α) (y : Fin n → β) :
    List.zipWith f (List.ofFn x) (List.ofFn y)=List.ofFn (fun i => f (x i) (y i)) := by
  apply List.ext_getElem (by simp)
  intro j hj hk
  simp only [List.getElem_zipWith,List.getElem_ofFn]

theorem bit_weight (w : ZMod 4) (z : ZMod 2) :
    (if BinaryRowColumns.bit z then w else 0)=w*BinaryPhase.bitLift z := by
  rw [←BinaryRowColumns.scalar_bit z]
  have hzero : BinaryRowColumns.bit 0=false := by decide
  have hone : BinaryRowColumns.bit 1=true := by decide
  cases BinaryRowColumns.bit z <;> simp [BinaryRowColumns.scalar,hzero,hone]

private theorem signed_weighted_sum {n : ℕ} (ws : Fin n → ZMod 4)
    (bs : Fin n → Bool) (direction : Bool) :
    WeightedPhaseAccumulator.weightedSum
      (List.ofFn (fun i => if direction then -ws i else ws i)) (List.ofFn bs)=
      if direction then -(∑ i,if bs i then ws i else 0) else ∑ i,if bs i then ws i else 0 := by
  rw [WeightedPhaseAccumulator.weightedSum,zip_ofFn,List.sum_ofFn]
  cases direction
  · simp only [Bool.false_eq_true,ite_false]
  · simp only [ite_true]
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases bs i <;> simp

theorem weighted_phase (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) :
    WeightedPhaseAccumulator.weightedSum (weights edge) (bits input hslots edge k axis)=
      if direction edge then -(diagonal input hslots edge k axis) else diagonal input hslots edge k axis := by
  change WeightedPhaseAccumulator.weightedSum
    (List.ofFn (fun i => if direction edge then -weight edge i else weight edge i))
    (List.ofFn (fun i => BinaryRowColumns.bit (control input hslots edge k axis i)))=_
  rw [signed_weighted_sum]
  simp only [bit_weight]
  rfl

theorem readout (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) :
    ((WeightedPhaseAccumulator.accumulate 0 (weights edge) (bits input hslots edge k axis)).val : ZMod 4)=
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (target edge) (target_nondegenerate edge) (originalCoordinates input hslots k axis))-
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (source edge) (source_nondegenerate edge) (originalCoordinates input hslots k axis)) := by
  rw [WeightedPhaseAccumulator.accumulate_cast _ _ _ (lengths input hslots edge k axis),weighted_phase,
    CompactComplexPhasePhysical.original_phase]
  simp

def program (edge : Edge) := WeightedUnitPhase.program (weights edge)

theorem runs (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f)
    (xs : ℕ → List (Fin 2)) (b : ℕ) (hw : ∀ j,(xs j).length=b) :
    HoareTime (program edge)
      (fun v => v=WeightedUnitPhase.input (bits input hslots edge k axis) xs)
      (fun v => v=WeightedUnitPhase.output (weights edge) (bits input hslots edge k axis) xs)
      (2*dimension edge+12*b+46) := by
  have h := WeightedUnitPhase.runs (weights edge) (bits input hslots edge k axis)
    (lengths input hslots edge k axis) xs b hw
  have hl : (weights edge).length=dimension edge := List.length_ofFn
  rw [hl] at h
  exact h

theorem complex_phase (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f)
    (xs : ℕ → List (Fin 2)) (b n : ℕ) (hw : ∀ j,(xs j).length=b+1)
    (hguard : ∀ j : Fin 2,|ButterflySigned.signedValue b (xs j.val)|<(2^b : ℕ)) :
    let p := WeightedPhaseAccumulator.accumulate 0 (weights edge) (bits input hslots edge k axis)
    ButterflySigned.complexValue (ButterflySigned.signedValue b (UnitPhaseNumerator.words p 0 xs))
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words p 1 xs)) n=
      BinaryPhase.phase
        (BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
          (target edge) (target_nondegenerate edge) (originalCoordinates input hslots k axis))-
        BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
          (source edge) (source_nondegenerate edge) (originalCoordinates input hslots k axis)))*
      ButterflySigned.complexValue (ButterflySigned.signedValue b (xs 0)) (ButterflySigned.signedValue b (xs 1)) n := by
  dsimp only
  rw [UnitPhaseSigned.words_phase _ xs b n hw hguard,readout]

end
end IntegerMultBounds.Machine.CompactComplexPhaseControlCodec
