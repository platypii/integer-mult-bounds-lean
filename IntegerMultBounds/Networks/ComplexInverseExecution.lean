import IntegerMultBounds.Networks.ComplexFramedConjugation
import IntegerMultBounds.Networks.BinaryColumnConjugation

/-! The conjugated ORIGINAL corrected complex network computes the genuine
inverse full tensor, including every scratch wire. The source/sink corrections
are part of this identity; no claim about a physical tape wrapper is made. -/
namespace IntegerMultBounds.Networks.ComplexInverseExecution
noncomputable section

/-- The conjugated original label frame is its actual inverse. -/
theorem frameOf_conjugate (k : ℕ) (U : ComplexPhaseBudget.Label) :
    ComplexFramedConjugation.conjugatedFrame (ComplexFramedExecution.frameOf k U)=
      (ComplexFramedExecution.frameOf k U).symm := by
  apply LinearEquiv.ext
  intro f
  change BinaryColumnConjugation.conjugate
    (BinaryColumnFrame.rationalLabelFrame ComplexPhaseBudget.coordinateSymm k
      (LabelTransport.label (TensorCoordinates.coordinates 25) U)
      (BinaryColumnConjugation.conjugate f))=
    (BinaryColumnFrame.rationalLabelFrame ComplexPhaseBudget.coordinateSymm k
      (LabelTransport.label (TensorCoordinates.coordinates 25) U)).symm f
  rw [BinaryColumnConjugation.rational_label_conjugate,BinaryColumnConjugation.conjugate_twice]

/-- All original scalar gates and their order are retained; the conjugated
endpoint corrections give the true inverse transform on the entire bank. -/
theorem corrected_inverse_network (k : ℕ)
    (stored : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) k) :
    ComplexFramedConjugation.correctOutput k
      (FramedCircuit.run (ComplexFramedConjugation.network k)
        (ComplexFramedConjugation.correctInput k stored))=
      fun i => (ComplexEndpoints.fullFrame k).symm (stored i) := by
  rw [ComplexFramedConjugation.corrected_network_run]
  funext i
  change BinaryColumnConjugation.conjugate
    (BinaryColumnFrame.frameEquiv k BinaryPhase.weightPhase
      (BinaryColumnConjugation.conjugate (stored i)))=
    (BinaryColumnFrame.frameEquiv k BinaryPhase.weightPhase).symm (stored i)
  rw [BinaryColumnConjugation.frame_conjugate,BinaryColumnConjugation.conjugate_twice]

end
end IntegerMultBounds.Networks.ComplexInverseExecution
